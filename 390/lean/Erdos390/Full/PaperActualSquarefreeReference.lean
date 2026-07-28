import Erdos390.Full.PaperActualPrimePowerRelative
import Erdos390.Full.PaperBridgeNuisanceTiltFallback
import Erdos390.Full.SquarefreeReferenceOperatorIdentification
import Erdos390.Full.GuardDeletionSquarefreeProfiles
import Erdos390.Full.GuardSquarefreeErrorRate
import Erdos390.Full.FixedFiniteMixtureSignedSquarefree
import Erdos390.Full.PrimePowerSharpBandTransfer

/-!
# The actual bridge squarefree law and the canonical reference operator

This file closes two finite-probability identifications needed in Lemma 8.4.
First, a reciprocal signed profile for the medium-only law survives the
literal physical/head component tilt at the same reciprocal scale.  Second,
the partition-function-reweighted mixture of those component laws is exactly
the `BridgeData.tiltedLaw`, including the between-cell covariance.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open PrimePowerCovariance PrimePowerCovariance.BoundedValuationLaw
open OmittedTiltPairChamber PaperPrimePowerChamberError
open StructuredCells ValuationScoreDomination

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- The full-tilted law on one literal guard-deleted component, widened to
the same endpoint as the global bridge law. -/
def actualComponentValuationLaw [Nonempty Head]
    (xi : B.ParamSpace) (c : Cell Head) :
    BoundedValuationLaw (B.sampleData.SampleAt c) B.sampleEndpoint where
  probability :=
    (B.guardedCellProbability c).exponentialTilt
      (sigmaCellScore (B.scaledBridgeScore xi) c)
  value := fun m => (m : ℕ)
  value_pos := by
    intro m
    let sample : B.sampleData.Sample := ⟨c, m⟩
    simpa only [sample, StructuredSampleData.value] using
      B.sampleData.value_pos sample
  value_le := by
    intro m
    let sample : B.sampleData.Sample := ⟨c, m⟩
    simpa only [sample, StructuredSampleData.value] using
      B.sample_value_le_endpoint sample

@[simp] theorem actualComponentValuationLaw_probability [Nonempty Head]
    (xi : B.ParamSpace) (c : Cell Head) :
    (B.actualComponentValuationLaw xi c).probability =
      (B.guardedCellProbability c).exponentialTilt
        (sigmaCellScore (B.scaledBridgeScore xi) c) := rfl

@[simp] theorem actualComponentValuationLaw_value [Nonempty Head]
    (xi : B.ParamSpace) (c : Cell Head)
    (m : B.sampleData.SampleAt c) :
    (B.actualComponentValuationLaw xi c).value m = (m : ℕ) := rfl

/-- Replacing a finite set by an equal finite set does not change a uniform
valuation tilt or any divisor expectation.  This small transport lemma keeps
dependent nonemptiness proofs out of the marked-profile argument. -/
theorem uniformValuationTilt_expect_divInd_eq_of_finset_eq
    (S T : Finset ℕ) (hST : S = T)
    (hS : S.Nonempty) (hT : T.Nonempty)
    (primes : Finset ℕ) (eta : ℕ → ℝ) (logScale : ℝ) (D : ℕ) :
    ((uniformOnFinset S hS).exponentialTilt
        (fun m ↦ valuationScore primes eta logScale (m : ℕ))).expect
        (fun m ↦ divInd D (m : ℕ)) =
      ((uniformOnFinset T hT).exponentialTilt
        (fun m ↦ valuationScore primes eta logScale (m : ℕ))).expect
        (fun m ↦ divInd D (m : ℕ)) := by
  subst T
  have hp : hT = hS := Subsingleton.elim _ _
  subst hT
  rfl

/-- A compact effective-prime box gives a pointwise score bound on the
*unguarded* cell with a constant independent of the cell and of `n`. -/
theorem abs_unguardedCell_mediumScore_le [Nonempty Head]
    (xi : B.ParamSpace) (c : Cell Head) {C A : ℝ}
    (hC : 1 ≤ C) (hW : 1 < B.sampleData.W)
    (hhi : ∀ sigma, B.sampleData.hi sigma ≤
      physicalBound C B.sampleData.n)
    (hA : 0 ≤ A)
    (heta : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |B.effectivePrimeCoefficient xi p| ≤ A)
    (m : structuredCell (B.sampleData.pattern c.1)
      (B.sampleData.lo c.2) (B.sampleData.hi c.2)
      (yNat B.sampleData.n)) :
    |valuationScore (primeBand B.sampleData.n B.sampleData.W)
        (B.effectiveNatCoefficient xi) B.L (m : ℕ)| ≤
      A * PaperStatisticNorm.valuationLogCoefficient C B.sampleData.W := by
  have hmpos : 0 < (m : ℕ) :=
    pos_of_mem_smoothInterval (mem_structuredCell.mp m.property).1
  have hmhi : (m : ℕ) ≤ B.sampleData.hi c.2 :=
    (mem_smoothInterval.mp (mem_structuredCell.mp m.property).1).2.1
  have hmC : (m : ℕ) ≤ physicalBound C B.sampleData.n :=
    hmhi.trans (hhi c.2)
  have hpW : ∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
      B.sampleData.W ≤ p := by
    intro p hp
    exact (cutoff_lt_of_mem_primeBand hp).le
  have hetaNat : ∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
      |B.effectiveNatCoefficient xi p| ≤ A := by
    intro p hp
    rw [B.effectiveNatCoefficient_of_mem xi hp]
    exact heta ⟨p, hp⟩
  have hraw := ValuationTiltCell.abs_valuationScore_le_log_ratio
    (primeBand B.sampleData.n B.sampleData.W)
    (B.effectiveNatCoefficient xi) hmpos hmC hW hpW hA B.L_pos hetaNat
  have hlogW : 0 < Real.log (B.sampleData.W : ℝ) :=
    Real.log_pos (by exact_mod_cast hW)
  have hcoef : 0 ≤ A / B.L := div_nonneg hA B.L_pos.le
  calc
    |valuationScore (primeBand B.sampleData.n B.sampleData.W)
        (B.effectiveNatCoefficient xi) B.L (m : ℕ)| ≤
      (A / B.L) *
        (Real.log (physicalBound C B.sampleData.n : ℝ) /
          Real.log (B.sampleData.W : ℝ)) := hraw
    _ ≤ (A / B.L) *
        ((PaperStatisticNorm.physicalLogCoefficient C * B.L) /
          Real.log (B.sampleData.W : ℝ)) := by
      exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right
          (PaperStatisticNorm.BridgeData.log_physicalBound_le B hC)
          hlogW.le) hcoef
    _ = A * PaperStatisticNorm.valuationLogCoefficient C B.sampleData.W := by
      unfold PaperStatisticNorm.valuationLogCoefficient
      field_simp [B.L_pos.ne', hlogW.ne']

/-- The exponential reciprocal fallback used by the physical second tilt is
bounded by the same fixed effective-prime box constant as the raw medium
score.  In particular the ceiling has no dependence on `n` or on a moving
band cell. -/
theorem mediumFallbackExponent_le [Nonempty Head]
    (c : Cell Head) {C A : ℝ}
    (hC : 1 ≤ C) (hW : 1 < B.sampleData.W) (hA : 0 ≤ A)
    (hhi : B.sampleData.hi c.2 ≤
      physicalBound C B.sampleData.n) :
    (A / B.L) *
        (Real.log (B.sampleData.hi c.2 : ℝ) /
          Real.log (B.sampleData.W : ℝ)) ≤
      A * PaperStatisticNorm.valuationLogCoefficient C B.sampleData.W := by
  have hhiPos : (0 : ℝ) < B.sampleData.hi c.2 := by
    exact_mod_cast B.cell_hi_pos c
  have hboundPos : (0 : ℝ) < physicalBound C B.sampleData.n := by
    have hn : 0 < B.sampleData.n := Nat.zero_lt_of_lt B.n_gt_one
    have hnle : B.sampleData.n ≤ physicalBound C B.sampleData.n := by
      unfold physicalBound
      apply Nat.le_floor
      exact_mod_cast (show (B.sampleData.n : ℝ) ≤
        C * (B.sampleData.n : ℝ) by
          nlinarith [show (0 : ℝ) ≤ (B.sampleData.n : ℝ) by positivity])
    exact_mod_cast hn.trans_le hnle
  have hlogW : 0 < Real.log (B.sampleData.W : ℝ) :=
    Real.log_pos (by exact_mod_cast hW)
  have hlogHi : Real.log (B.sampleData.hi c.2 : ℝ) ≤
      PaperStatisticNorm.physicalLogCoefficient C * B.L := by
    exact (Real.log_le_log hhiPos (by exact_mod_cast hhi)).trans
      (PaperStatisticNorm.BridgeData.log_physicalBound_le B hC)
  have hratio :
      Real.log (B.sampleData.hi c.2 : ℝ) /
          Real.log (B.sampleData.W : ℝ) ≤
        (PaperStatisticNorm.physicalLogCoefficient C * B.L) /
          Real.log (B.sampleData.W : ℝ) :=
    div_le_div_of_nonneg_right hlogHi hlogW.le
  calc
    (A / B.L) *
          (Real.log (B.sampleData.hi c.2 : ℝ) /
            Real.log (B.sampleData.W : ℝ)) ≤
        (A / B.L) *
          ((PaperStatisticNorm.physicalLogCoefficient C * B.L) /
            Real.log (B.sampleData.W : ℝ)) :=
      mul_le_mul_of_nonneg_left hratio (div_nonneg hA B.L_pos.le)
    _ = A * PaperStatisticNorm.valuationLogCoefficient C
          B.sampleData.W := by
      unfold PaperStatisticNorm.valuationLogCoefficient
      field_simp [B.L_pos.ne', hlogW.ne']

/-- The literal medium-only bridge law is the conditional guard deletion of
the corresponding unguarded structured-cell tilt.  Consequently signed
profiles on the unguarded cell transfer to `cellMediumLaw` with the explicit
reciprocal guard cost. -/
theorem cellMediumLaw_squarefree_profiles_of_unguarded [Nonempty Head]
    (xi : B.ParamSpace) (c : Cell Head) {K E : ℝ}
    (hS : (structuredCell (B.sampleData.pattern c.1)
      (B.sampleData.lo c.2) (B.sampleData.hi c.2)
      (yNat B.sampleData.n)).Nonempty)
    (hscore : ∀ m : structuredCell (B.sampleData.pattern c.1)
        (B.sampleData.lo c.2) (B.sampleData.hi c.2)
        (yNat B.sampleData.n),
      |valuationScore (primeBand B.sampleData.n B.sampleData.W)
          (B.effectiveNatCoefficient xi) B.L (m : ℕ)| ≤ K)
    (hsmallCensus :
      Real.exp (2 * K) * (B.sampleData.guards.card : ℝ) /
        ((structuredCell (B.sampleData.pattern c.1)
          (B.sampleData.lo c.2) (B.sampleData.hi c.2)
          (yNat B.sampleData.n)).card : ℝ) ≤ (1 : ℝ) / 2)
    (hpair : ∀ p, p ∈ primeBand B.sampleData.n B.sampleData.W →
      ∀ q, q ∈ (primeBand B.sampleData.n B.sampleData.W).erase p →
      |((uniformOnFinset
          (structuredCell (B.sampleData.pattern c.1)
            (B.sampleData.lo c.2) (B.sampleData.hi c.2)
            (yNat B.sampleData.n))
          hS).exponentialTilt
          (fun m ↦ valuationScore
            (primeBand B.sampleData.n B.sampleData.W)
            (B.effectiveNatCoefficient xi) B.L (m : ℕ))).expect
          (fun m ↦ divInd (pairPower p q 1 1) (m : ℕ)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n
          (pairPower p q 1 1)| ≤ E * pairWeight p q 1 1)
    (hsingle : ∀ p, p ∈ primeBand B.sampleData.n B.sampleData.W →
      |((uniformOnFinset
          (structuredCell (B.sampleData.pattern c.1)
            (B.sampleData.lo c.2) (B.sampleData.hi c.2)
            (yNat B.sampleData.n))
          hS).exponentialTilt
          (fun m ↦ valuationScore
            (primeBand B.sampleData.n B.sampleData.W)
            (B.effectiveNatCoefficient xi) B.L (m : ℕ))).expect
          (fun m ↦ divInd p (m : ℕ)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n p| ≤
          E * singleWeight p 1) :
    (∀ p, p ∈ primeBand B.sampleData.n B.sampleData.W →
      ∀ q, q ∈ (primeBand B.sampleData.n B.sampleData.W).erase p →
      |(B.cellMediumLaw xi c).expect
          (fun m ↦ divInd (pairPower p q 1 1) (m : ℕ)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n
          (pairPower p q 1 1)| ≤
        (E + GuardDeletionSquarefreeProfiles.guardSquarefreeError
          (structuredCell (B.sampleData.pattern c.1)
            (B.sampleData.lo c.2) (B.sampleData.hi c.2)
            (yNat B.sampleData.n)) B.sampleData.guards K B.sampleData.n) *
          pairWeight p q 1 1) ∧
    (∀ p, p ∈ primeBand B.sampleData.n B.sampleData.W →
      |(B.cellMediumLaw xi c).expect (fun m ↦ divInd p (m : ℕ)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n p| ≤
        (E + GuardDeletionSquarefreeProfiles.guardSquarefreeError
          (structuredCell (B.sampleData.pattern c.1)
            (B.sampleData.lo c.2) (B.sampleData.hi c.2)
            (yNat B.sampleData.n)) B.sampleData.guards K B.sampleData.n) *
          singleWeight p 1) := by
  let S := structuredCell (B.sampleData.pattern c.1)
    (B.sampleData.lo c.2) (B.sampleData.hi c.2) (yNat B.sampleData.n)
  have hR : (S \ B.sampleData.guards).Nonempty := by
    simpa only [S, StructuredSampleData.cellFinset] using
      B.sampleData.cell_nonempty c
  have hS' : S.Nonempty := by simpa only [S] using hS
  let score : S → ℝ := fun m ↦
    valuationScore (primeBand B.sampleData.n B.sampleData.W)
      (B.effectiveNatCoefficient xi) B.L (m : ℕ)
  have hprofiles :=
    GuardDeletionSquarefreeProfiles.remaining_tilt_squarefree_profiles
      S B.sampleData.guards hS' hR score K
      (by simpa only [score, S] using hscore)
      hsmallCensus (by simpa only [S, score] using hpair)
      (by simpa only [S, score] using hsingle)
  have hmedium : B.cellMediumLaw xi c =
      (uniformOnFinset (S \ B.sampleData.guards) hR).exponentialTilt
        (fun z ↦ score
          (GuardedUniformCell.remainingEmbedding S B.sampleData.guards z)) := by
    unfold cellMediumLaw guardedCellProbability
    let hR₀ : (S \ B.sampleData.guards).Nonempty := by
      simpa only [S, StructuredSampleData.cellFinset] using
        B.sampleData.cell_nonempty c
    change
      (uniformOnFinset (S \ B.sampleData.guards) hR₀).exponentialTilt
          (sigmaCellScore (B.scaledMediumScore xi) c) =
        (uniformOnFinset (S \ B.sampleData.guards) hR).exponentialTilt
          (fun z ↦ score
            (GuardedUniformCell.remainingEmbedding S B.sampleData.guards z))
    have hbase : uniformOnFinset (S \ B.sampleData.guards) hR₀ =
        uniformOnFinset (S \ B.sampleData.guards) hR := by
      apply FiniteProbability.eq_of_mass_eq
      rfl
    rw [hbase]
    apply congrArg ((uniformOnFinset (S \ B.sampleData.guards) hR).exponentialTilt)
    funext z
    exact B.sigmaCellScore_scaledMedium_eq_valuationScore xi c z |>.trans rfl
  rw [hmedium]
  simpa only [S, score] using hprofiles

/-- Uniform signed profiles for the actual medium-tilted guarded bridge
cells.  The profile is derived from the fixed finite marked-cell theorem and
the concrete ledger census.  Its error, including guard deletion, still
vanishes after multiplication by `log (L n)`.

Only structural identifications of `sampleData` with the canonical physical
cells occur as hypotheses; no probability, covariance, operator, or inverse
estimate is assumed. -/
theorem exists_boxIndependent_actual_medium_signed_profiles
    [Nonempty Head]
    (Phead : Head → HeadPattern.Pattern)
    (I : PaperGuardCensus.PhysicalIntervals) (Cmax : ℝ)
    (hupperOne : ∀ sigma, 1 ≤ I.upper sigma)
    (hupperMax : ∀ sigma, I.upper sigma ≤ Cmax)
    (Cprom Cbank : ℕ)
    (ledger : ∀ n, PaperGuardCensus.Ledger n Cprom Cbank) :
    ∀ W : ℕ, 1 < W →
      (∀ h, ∀ p ∈ (Phead h).primes, p ≤ W) →
    ∀ Acoef : ℝ, 0 ≤ Acoef →
    ∃ profileError : ℕ → ℝ,
      (∀ n, 0 ≤ profileError n) ∧
      Filter.Tendsto profileError Filter.atTop (nhds 0) ∧
      Filter.Tendsto (fun n : ℕ ↦ profileError n * Real.log (Scale.L n))
        Filter.atTop (nhds 0) ∧
      ∃ N₀ : ℕ,
        ∀ {Band : Type*} [Fintype Band] [DecidableEq Band]
          (B : BridgeData Head Band) (xi : B.ParamSpace),
          N₀ ≤ B.sampleData.n →
          B.sampleData.pattern = Phead →
          (∀ sigma, B.sampleData.lo sigma =
            physicalBound (I.lower sigma) B.sampleData.n) →
          (∀ sigma, B.sampleData.hi sigma =
            physicalBound (I.upper sigma) B.sampleData.n) →
          B.sampleData.guards = (ledger B.sampleData.n).guards →
          (∀ p : BandPrime B.sampleData.n B.sampleData.W,
            |B.effectivePrimeCoefficient xi p| ≤ Acoef) →
          B.sampleData.W = W →
          (∀ c p, p ∈ primeBand B.sampleData.n B.sampleData.W →
            ∀ q, q ∈ (primeBand B.sampleData.n B.sampleData.W).erase p →
            |(B.cellMediumLaw xi c).expect
                (fun m ↦ divInd (pairPower p q 1 1) (m : ℕ)) -
              PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n
                (pairPower p q 1 1)| ≤
              profileError B.sampleData.n * pairWeight p q 1 1) ∧
          (∀ c p, p ∈ primeBand B.sampleData.n B.sampleData.W →
            |(B.cellMediumLaw xi c).expect
                (fun m ↦ divInd p (m : ℕ)) -
              PaperScaleMarkedCell.paperDivisibilityMain
                B.sampleData.n p| ≤
              profileError B.sampleData.n * singleWeight p 1) := by
  intro W hW hsupport Acoef hAcoef
  let H : Cell Head → HeadPattern.Pattern := fun c ↦ Phead c.1
  let Alower : Cell Head → ℝ := fun c ↦ I.lower c.2
  let Cupper : Cell Head → ℝ := fun c ↦ I.upper c.2
  obtain ⟨rawError, hraw0, hrawT, hrawRate, Nraw, hraw⟩ :=
    FixedFiniteMixtureSignedSquarefree.exists_boxIndependent_fixedFiniteMixture_signed_profiles
      H Alower Cupper Cmax
      (fun c ↦ I.lower_pos c.2) (fun c ↦ I.lower_lt_upper c.2)
      (fun c ↦ hupperOne c.2) (fun c ↦ hupperMax c.2)
      W hW (fun c ↦ hsupport c.1) Acoef hAcoef
  let K := Acoef * PaperStatisticNorm.valuationLogCoefficient Cmax W
  let guardError : ℕ → ℝ :=
    Erdos390.Full.GuardSquarefreeErrorRate.canonicalGuardSquarefreeError
      Phead I ledger K
  let profileError : ℕ → ℝ := fun n ↦ rawError n + guardError n
  have hCmax : 1 ≤ Cmax := (hupperOne .minus).trans (hupperMax .minus)
  have hguard0 (n : ℕ) : 0 ≤ guardError n := by
    exact Erdos390.Full.GuardSquarefreeErrorRate.canonicalGuardSquarefreeError_nonneg
      Phead I ledger K n
  have hguardT : Filter.Tendsto guardError Filter.atTop (nhds 0) := by
    exact Erdos390.Full.GuardSquarefreeErrorRate.tendsto_canonicalGuardSquarefreeError_zero
      Phead I ledger K
  have hguardRate : Filter.Tendsto
      (fun n : ℕ ↦ guardError n * Real.log (Scale.L n))
        Filter.atTop (nhds 0) := by
    exact Erdos390.Full.GuardSquarefreeErrorRate.tendsto_canonicalGuardSquarefreeError_mul_logL_zero
      Phead I ledger K
  have hprofile0 (n : ℕ) : 0 ≤ profileError n := by
    exact add_nonneg (hraw0 n) (hguard0 n)
  have hprofileT : Filter.Tendsto profileError Filter.atTop (nhds 0) := by
    simpa only [profileError, add_zero] using hrawT.add hguardT
  have hprofileRate : Filter.Tendsto
      (fun n : ℕ ↦ profileError n * Real.log (Scale.L n))
        Filter.atTop (nhds 0) := by
    simpa only [profileError, add_mul, add_zero] using
      hrawRate.add hguardRate
  have hsmallEvent :=
    Erdos390.Full.GuardSquarefreeErrorRate.eventually_exp_two_mul_guardRatio_rawCell_le_half
      Phead I Cprom Cbank ledger K
  obtain ⟨Nguard, hNguard⟩ := (Filter.eventually_atTop.1 hsmallEvent)
  let N₀ := max Nraw Nguard
  refine ⟨profileError, hprofile0, hprofileT, hprofileRate, N₀, ?_⟩
  intro Band _instBand _instBandDec B xi hN hpattern hlo hhi hguards heta hBW
  have hNraw : Nraw ≤ B.sampleData.n :=
    (Nat.le_max_left _ _).trans hN
  have hNguard' : Nguard ≤ B.sampleData.n :=
    (Nat.le_max_right _ _).trans hN
  have hetaNat : ∀ z ∈ primeBand B.sampleData.n W,
      |B.effectiveNatCoefficient xi z| ≤ Acoef := by
    intro z hz
    have hzB : z ∈ primeBand B.sampleData.n B.sampleData.W := by
      simpa only [hBW] using hz
    rw [B.effectiveNatCoefficient_of_mem xi hzB]
    exact heta ⟨z, hzB⟩
  obtain ⟨hSraw, hrawProfiles⟩ :=
    hraw (B.effectiveNatCoefficient xi) hNraw hetaNat
  have hrawProfiles' := hrawProfiles hSraw
  have hsmallAll := hNguard B.sampleData.n hNguard'
  have hhiC : ∀ sigma, B.sampleData.hi sigma ≤
      physicalBound Cmax B.sampleData.n := by
    intro sigma
    rw [hhi sigma]
    exact FixedFiniteMixtureFullUniform.physicalBound_mono
      (hupperMax sigma) B.sampleData.n
  let Sfixed : Cell Head → Finset ℕ := fun c ↦
    PaperGuardCensus.rawCell Phead I B.sampleData.n c
  let Sbridge : Cell Head → Finset ℕ := fun c ↦
    structuredCell (B.sampleData.pattern c.1)
      (B.sampleData.lo c.2) (B.sampleData.hi c.2) (yNat B.sampleData.n)
  have hSfixed (c : Cell Head) : (Sfixed c).Nonempty := by
    simpa only [Sfixed, PaperGuardCensus.rawCell, H, Alower, Cupper] using
      hSraw c
  have hSbridge (c : Cell Head) : (Sbridge c).Nonempty := by
    obtain ⟨m, hm⟩ := B.sampleData.cell_nonempty c
    exact ⟨m, by simpa only [Sbridge] using (Finset.mem_sdiff.mp hm).1⟩
  have hcellEq (c : Cell Head) : Sfixed c = Sbridge c := by
    simp only [Sfixed, Sbridge, PaperGuardCensus.rawCell,
      hpattern, hlo, hhi]
  have hrawPairBridge : ∀ c p,
      p ∈ primeBand B.sampleData.n B.sampleData.W →
      ∀ q, q ∈ (primeBand B.sampleData.n B.sampleData.W).erase p →
      |((uniformOnFinset (Sbridge c) (hSbridge c)).exponentialTilt
          (fun m ↦ valuationScore
            (primeBand B.sampleData.n B.sampleData.W)
            (B.effectiveNatCoefficient xi) B.L (m : ℕ))).expect
          (fun m ↦ divInd (pairPower p q 1 1) (m : ℕ)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n
          (pairPower p q 1 1)| ≤
        rawError B.sampleData.n * pairWeight p q 1 1 := by
    intro c p hp q hq
    have hpW : p ∈ primeBand B.sampleData.n W := by
      simpa only [hBW] using hp
    have hqW : q ∈ (primeBand B.sampleData.n W).erase p := by
      simpa only [hBW] using hq
    have hpY := le_yNat_of_mem_primeBand hpW
    have hqY := le_yNat_of_mem_primeBand (Finset.mem_erase.mp hqW).2
    have hyPos : 0 < yNat B.sampleData.n :=
      (prime_of_mem_primeBand hpW).pos.trans_le hpY
    have hpqSq : p * q ≤ yNat B.sampleData.n ^ 2 := by
      simpa only [pow_two] using Nat.mul_le_mul hpY hqY
    have hpow : pairPower p q 1 1 ≤ yNat B.sampleData.n ^ 4 := by
      unfold pairPower
      norm_num
      exact hpqSq.trans (Nat.pow_le_pow_right hyPos (by omega : 2 ≤ 4))
    have hrawCell := hrawProfiles'.1 c p hpW q hqW 1 1 hpow
    have hrawCell' :
        |((uniformOnFinset (Sfixed c) (hSfixed c)).exponentialTilt
            (fun m ↦ valuationScore (primeBand B.sampleData.n W)
              (B.effectiveNatCoefficient xi) (Scale.L B.sampleData.n)
              (m : ℕ))).expect
            (fun m ↦ divInd (pairPower p q 1 1) (m : ℕ)) -
          PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n
            (pairPower p q 1 1)| ≤
          rawError B.sampleData.n * pairWeight p q 1 1 := by
      simpa only [Sfixed, PaperGuardCensus.rawCell, H, Alower, Cupper,
        PrimePowerCovariance.BoundedValuationLaw.widen_probability,
        PrimePowerCovariance.BoundedValuationLaw.widen_value,
        StructuredCellValuationLaw.valuationTilt_probability,
        StructuredCellValuationLaw.valuationTilt_value] using hrawCell
    have heq := uniformValuationTilt_expect_divInd_eq_of_finset_eq
      (Sfixed c) (Sbridge c) (hcellEq c) (hSfixed c) (hSbridge c)
      (primeBand B.sampleData.n W) (B.effectiveNatCoefficient xi)
      (Scale.L B.sampleData.n) (pairPower p q 1 1)
    have heq' :
        ((uniformOnFinset (Sfixed c) (hSfixed c)).exponentialTilt
            (fun m ↦ valuationScore (primeBand B.sampleData.n W)
              (B.effectiveNatCoefficient xi) (Scale.L B.sampleData.n)
              (m : ℕ))).expect
            (fun m ↦ divInd (pairPower p q 1 1) (m : ℕ)) =
          ((uniformOnFinset (Sbridge c) (hSbridge c)).exponentialTilt
            (fun m ↦ valuationScore
              (primeBand B.sampleData.n B.sampleData.W)
              (B.effectiveNatCoefficient xi) B.L (m : ℕ))).expect
            (fun m ↦ divInd (pairPower p q 1 1) (m : ℕ)) := by
      simpa only [hBW, BridgeData.L, Scale.L] using heq
    rw [← heq']
    exact hrawCell'
  have hrawSingleBridge : ∀ c p,
      p ∈ primeBand B.sampleData.n B.sampleData.W →
      |((uniformOnFinset (Sbridge c) (hSbridge c)).exponentialTilt
          (fun m ↦ valuationScore
            (primeBand B.sampleData.n B.sampleData.W)
            (B.effectiveNatCoefficient xi) B.L (m : ℕ))).expect
          (fun m ↦ divInd p (m : ℕ)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n p| ≤
        rawError B.sampleData.n * singleWeight p 1 := by
    intro c p hp
    have hpW : p ∈ primeBand B.sampleData.n W := by
      simpa only [hBW] using hp
    have hrawCell := hrawProfiles'.2 c p hpW
    have hrawCell' :
        |((uniformOnFinset (Sfixed c) (hSfixed c)).exponentialTilt
            (fun m ↦ valuationScore (primeBand B.sampleData.n W)
              (B.effectiveNatCoefficient xi) (Scale.L B.sampleData.n)
              (m : ℕ))).expect (fun m ↦ divInd p (m : ℕ)) -
          PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n p| ≤
          rawError B.sampleData.n * singleWeight p 1 := by
      simpa only [Sfixed, PaperGuardCensus.rawCell, H, Alower, Cupper,
        PrimePowerCovariance.BoundedValuationLaw.widen_probability,
        PrimePowerCovariance.BoundedValuationLaw.widen_value,
        StructuredCellValuationLaw.valuationTilt_probability,
        StructuredCellValuationLaw.valuationTilt_value] using hrawCell
    have heq := uniformValuationTilt_expect_divInd_eq_of_finset_eq
      (Sfixed c) (Sbridge c) (hcellEq c) (hSfixed c) (hSbridge c)
      (primeBand B.sampleData.n W) (B.effectiveNatCoefficient xi)
      (Scale.L B.sampleData.n) p
    have heq' :
        ((uniformOnFinset (Sfixed c) (hSfixed c)).exponentialTilt
            (fun m ↦ valuationScore (primeBand B.sampleData.n W)
              (B.effectiveNatCoefficient xi) (Scale.L B.sampleData.n)
              (m : ℕ))).expect (fun m ↦ divInd p (m : ℕ)) =
          ((uniformOnFinset (Sbridge c) (hSbridge c)).exponentialTilt
            (fun m ↦ valuationScore
              (primeBand B.sampleData.n B.sampleData.W)
              (B.effectiveNatCoefficient xi) B.L (m : ℕ))).expect
            (fun m ↦ divInd p (m : ℕ)) := by
      simpa only [hBW, BridgeData.L, Scale.L] using heq
    rw [← heq']
    exact hrawCell'
  have hscoreAll (c : Cell Head) : ∀ m : Sbridge c,
      |valuationScore (primeBand B.sampleData.n B.sampleData.W)
          (B.effectiveNatCoefficient xi) B.L (m : ℕ)| ≤ K := by
    intro m
    simpa only [Sbridge, K, hBW] using
      (B.abs_unguardedCell_mediumScore_le xi c hCmax
        (by simpa only [hBW] using hW) hhiC hAcoef heta m)
  have hsmallBridge (c : Cell Head) : Real.exp (2 * K) *
      (B.sampleData.guards.card : ℝ) / ((Sbridge c).card : ℝ) ≤
        (1 : ℝ) / 2 := by
    have hcsmall := hsmallAll c
    simpa only [Sbridge, hpattern, hlo, hhi, hguards,
      PaperGuardCensus.rawCell] using hcsmall
  have hguardCell (c : Cell Head) :
      GuardDeletionSquarefreeProfiles.guardSquarefreeError
          (Sbridge c) B.sampleData.guards K B.sampleData.n ≤
        guardError B.sampleData.n := by
    have hsum := Finset.single_le_sum
      (fun c' hc' ↦ GuardDeletionSquarefreeProfiles.guardSquarefreeError_nonneg
        (PaperGuardCensus.rawCell Phead I B.sampleData.n c')
        (ledger B.sampleData.n).guards K B.sampleData.n)
      (Finset.mem_univ c)
    simpa only [Sbridge, guardError,
      Erdos390.Full.GuardSquarefreeErrorRate.canonicalGuardSquarefreeError,
      hpattern, hlo, hhi, hguards, PaperGuardCensus.rawCell] using hsum
  have hcoeff (c : Cell Head) : rawError B.sampleData.n +
      GuardDeletionSquarefreeProfiles.guardSquarefreeError
          (Sbridge c) B.sampleData.guards K B.sampleData.n ≤
        profileError B.sampleData.n := by
    dsimp only [profileError]
    exact add_le_add_right (hguardCell c) _
  constructor
  · intro c p hp q hq
    have hlocal := B.cellMediumLaw_squarefree_profiles_of_unguarded
      xi c (by simpa only [Sbridge] using hSbridge c)
      (by simpa only [Sbridge] using hscoreAll c)
      (by simpa only [Sbridge] using hsmallBridge c)
      (by simpa only [Sbridge] using hrawPairBridge c)
      (by simpa only [Sbridge] using hrawSingleBridge c)
    exact (hlocal.1 p hp q hq).trans
      (mul_le_mul_of_nonneg_right (hcoeff c) (pairWeight_nonneg p q 1 1))
  · intro c p hp
    have hlocal := B.cellMediumLaw_squarefree_profiles_of_unguarded
      xi c (by simpa only [Sbridge] using hSbridge c)
      (by simpa only [Sbridge] using hscoreAll c)
      (by simpa only [Sbridge] using hsmallBridge c)
      (by simpa only [Sbridge] using hrawPairBridge c)
      (by simpa only [Sbridge] using hrawSingleBridge c)
    exact (hlocal.2 p hp).trans
      (mul_le_mul_of_nonneg_right (hcoeff c) (singleWeight_nonneg p 1))

/-- Adding the physical/head component tilt to a common signed medium
profile costs at most `4 epsilon G` in the paper's profile normalization.
The factor four is forced by the one-prime normalization
`singleWeight p 1 = 2/p`; it also dominates the two-prime cost. -/
theorem actualComponent_squarefree_profiles_of_medium [Nonempty Head]
    (xi : B.ParamSpace) (c : Cell Head)
    {Emedium rho A Aphys Kphys : ℝ}
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
    (hsmall : 8 * (Aphys * Kphys / B.L) ≤ 1)
    (hpair : ∀ p, p ∈ primeBand B.sampleData.n B.sampleData.W →
      ∀ q, q ∈ (primeBand B.sampleData.n B.sampleData.W).erase p →
      |(B.cellMediumLaw xi c).expect
          (fun m ↦ divInd (pairPower p q 1 1) (m : ℕ)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n
          (pairPower p q 1 1)| ≤
        Emedium * pairWeight p q 1 1)
    (hsingle : ∀ p, p ∈ primeBand B.sampleData.n B.sampleData.W →
      |(B.cellMediumLaw xi c).expect (fun m ↦ divInd p (m : ℕ)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n p| ≤
        Emedium * singleWeight p 1) :
    let epsilon := Aphys * Kphys / B.L
    let G := Real.exp (2 * ((A / B.L) *
      (Real.log (B.sampleData.hi c.2 : ℝ) /
        Real.log (B.sampleData.W : ℝ)))) / rho
    (∀ p, p ∈ primeBand B.sampleData.n B.sampleData.W →
      ∀ q, q ∈ (primeBand B.sampleData.n B.sampleData.W).erase p →
      |(B.actualComponentValuationLaw xi c).probability.expect
          (fun m ↦ divInd (pairPower p q 1 1)
            ((B.actualComponentValuationLaw xi c).value m)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n
          (pairPower p q 1 1)| ≤
        (Emedium + 4 * epsilon * G) * pairWeight p q 1 1) ∧
    (∀ p, p ∈ primeBand B.sampleData.n B.sampleData.W →
      |(B.actualComponentValuationLaw xi c).probability.expect
          (fun m ↦ divInd p
            ((B.actualComponentValuationLaw xi c).value m)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n p| ≤
        (Emedium + 4 * epsilon * G) * singleWeight p 1) := by
  dsimp only
  let epsilon := Aphys * Kphys / B.L
  let G := Real.exp (2 * ((A / B.L) *
    (Real.log (B.sampleData.hi c.2 : ℝ) /
      Real.log (B.sampleData.W : ℝ)))) / rho
  have hepsilon0 : 0 ≤ epsilon := by
    dsimp only [epsilon]
    exact div_nonneg (mul_nonneg hAphys0 hKphys0) B.L_pos.le
  have hG0 : 0 ≤ G := by
    dsimp only [G]
    exact div_nonneg (Real.exp_pos _).le hrho.le
  constructor
  · intro p hp q hq
    have hqBand := (Finset.mem_erase.mp hq).2
    have hpPrime := prime_of_mem_primeBand hp
    have hqPrime := prime_of_mem_primeBand hqBand
    have hD : 0 < pairPower p q 1 1 := by
      unfold pairPower
      simpa only [pow_one] using Nat.mul_pos hpPrime.pos hqPrime.pos
    have htilt := B.abs_guardedCell_fullTilt_expect_divInd_sub_medium_le
      xi c hD hA hW hrho hcard heta hAphys0 hKphys0 hAphys hKphys hsmall
    have htilt' :
        |(B.actualComponentValuationLaw xi c).probability.expect
              (fun m ↦ divInd (pairPower p q 1 1)
                ((B.actualComponentValuationLaw xi c).value m)) -
            (B.cellMediumLaw xi c).expect
              (fun m ↦ divInd (pairPower p q 1 1) (m : ℕ))| ≤
          8 * epsilon * (G * (1 / (pairPower p q 1 1 : ℝ))) := by
      simpa only [actualComponentValuationLaw_probability,
        actualComponentValuationLaw_value, epsilon, G] using htilt
    have hphysical :
        8 * epsilon * (G * (1 / (pairPower p q 1 1 : ℝ))) ≤
          (4 * epsilon * G) * pairWeight p q 1 1 := by
      unfold pairPower pairWeight
      norm_num
      have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpPrime.pos
      have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hqPrime.pos
      field_simp [hp0.ne', hq0.ne']
      nlinarith [hepsilon0, hG0]
    calc
      |(B.actualComponentValuationLaw xi c).probability.expect
            (fun m ↦ divInd (pairPower p q 1 1)
              ((B.actualComponentValuationLaw xi c).value m)) -
          PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n
            (pairPower p q 1 1)| ≤
        |(B.actualComponentValuationLaw xi c).probability.expect
              (fun m ↦ divInd (pairPower p q 1 1)
                ((B.actualComponentValuationLaw xi c).value m)) -
            (B.cellMediumLaw xi c).expect
              (fun m ↦ divInd (pairPower p q 1 1) (m : ℕ))| +
          |(B.cellMediumLaw xi c).expect
              (fun m ↦ divInd (pairPower p q 1 1) (m : ℕ)) -
            PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n
              (pairPower p q 1 1)| := by
          calc
            _ = |((B.actualComponentValuationLaw xi c).probability.expect
                    (fun m ↦ divInd (pairPower p q 1 1)
                      ((B.actualComponentValuationLaw xi c).value m)) -
                  (B.cellMediumLaw xi c).expect
                    (fun m ↦ divInd (pairPower p q 1 1) (m : ℕ))) +
                ((B.cellMediumLaw xi c).expect
                    (fun m ↦ divInd (pairPower p q 1 1) (m : ℕ)) -
                  PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n
                    (pairPower p q 1 1))| := by ring_nf
            _ ≤ _ := abs_add_le _ _
      _ ≤ (4 * epsilon * G) * pairWeight p q 1 1 +
          Emedium * pairWeight p q 1 1 :=
        add_le_add (htilt'.trans hphysical) (hpair p hp q hq)
      _ = (Emedium + 4 * epsilon * G) * pairWeight p q 1 1 := by ring
  · intro p hp
    have hpPrime := prime_of_mem_primeBand hp
    have htilt := B.abs_guardedCell_fullTilt_expect_divInd_sub_medium_le
      xi c hpPrime.pos hA hW hrho hcard heta hAphys0 hKphys0
      hAphys hKphys hsmall
    have htilt' :
        |(B.actualComponentValuationLaw xi c).probability.expect
              (fun m ↦ divInd p
                ((B.actualComponentValuationLaw xi c).value m)) -
            (B.cellMediumLaw xi c).expect (fun m ↦ divInd p (m : ℕ))| ≤
          8 * epsilon * (G * (1 / (p : ℝ))) := by
      simpa only [actualComponentValuationLaw_probability,
        actualComponentValuationLaw_value, epsilon, G] using htilt
    have hphysical : 8 * epsilon * (G * (1 / (p : ℝ))) =
        (4 * epsilon * G) * singleWeight p 1 := by
      unfold singleWeight
      norm_num
      ring
    calc
      |(B.actualComponentValuationLaw xi c).probability.expect
            (fun m ↦ divInd p
              ((B.actualComponentValuationLaw xi c).value m)) -
          PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n p| ≤
        |(B.actualComponentValuationLaw xi c).probability.expect
              (fun m ↦ divInd p
                ((B.actualComponentValuationLaw xi c).value m)) -
            (B.cellMediumLaw xi c).expect (fun m ↦ divInd p (m : ℕ))| +
          |(B.cellMediumLaw xi c).expect (fun m ↦ divInd p (m : ℕ)) -
            PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n p| := by
          calc
            _ = |((B.actualComponentValuationLaw xi c).probability.expect
                    (fun m ↦ divInd p
                      ((B.actualComponentValuationLaw xi c).value m)) -
                  (B.cellMediumLaw xi c).expect
                    (fun m ↦ divInd p (m : ℕ))) +
                ((B.cellMediumLaw xi c).expect
                    (fun m ↦ divInd p (m : ℕ)) -
                  PaperScaleMarkedCell.paperDivisibilityMain
                    B.sampleData.n p)| := by ring_nf
            _ ≤ _ := abs_add_le _ _
      _ ≤ (4 * epsilon * G) * singleWeight p 1 +
          Emedium * singleWeight p 1 :=
        add_le_add (htilt'.trans hphysical.le) (hsingle p hp)
      _ = (Emedium + 4 * epsilon * G) * singleWeight p 1 := by ring

/-- Uniform signed profiles for the literal full component laws.  This is
the finite-`n` attachment needed before taking the exact sigma mixture: raw
marked-cell asymptotics, guard deletion, and the physical second tilt are
all included in one error which is `o(1 / log L)`.

Every constant is selected from `Phead`, the two fixed physical intervals,
the fixed cutoff, and the preselected coefficient box.  No constant depends
on `n`, on a moving band cell, or on a subsequently chosen bridge law. -/
theorem exists_boxIndependent_actual_component_signed_profiles
    [Nonempty Head]
    (Phead : Head → HeadPattern.Pattern)
    (I : PaperGuardCensus.PhysicalIntervals) (Cmax : ℝ)
    (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
    (hupperMax : ∀ sigma, I.upper sigma ≤ Cmax)
    (Cprom Cbank : ℕ)
    (ledger : ∀ n, PaperGuardCensus.Ledger n Cprom Cbank) :
    ∀ W : ℕ, 1 < W →
      (∀ h, ∀ p ∈ (Phead h).primes, p ≤ W) →
    ∀ Acoef Aphys : ℝ, 0 ≤ Acoef → 0 ≤ Aphys →
    ∃ profileError : ℕ → ℝ,
      (∀ n, 0 ≤ profileError n) ∧
      Filter.Tendsto profileError Filter.atTop (nhds 0) ∧
      Filter.Tendsto (fun n : ℕ ↦ profileError n * Real.log (Scale.L n))
        Filter.atTop (nhds 0) ∧
      ∃ N₀ : ℕ,
        ∀ {Band : Type*} [Fintype Band] [DecidableEq Band]
          (B : BridgeData Head Band) (xi : B.ParamSpace),
          N₀ ≤ B.sampleData.n →
          B.sampleData.pattern = Phead →
          (∀ sigma, B.sampleData.lo sigma =
            physicalBound (I.lower sigma) B.sampleData.n) →
          (∀ sigma, B.sampleData.hi sigma =
            physicalBound (I.upper sigma) B.sampleData.n) →
          B.sampleData.guards = (ledger B.sampleData.n).guards →
          (∀ p : BandPrime B.sampleData.n B.sampleData.W,
            |B.effectivePrimeCoefficient xi p| ≤ Acoef) →
          |xi MomentCoord.physical| ≤ Aphys →
          B.sampleData.W = W →
          (∀ c p, p ∈ primeBand B.sampleData.n B.sampleData.W →
            ∀ q, q ∈ (primeBand B.sampleData.n B.sampleData.W).erase p →
            |(B.actualComponentValuationLaw xi c).probability.expect
                (fun m ↦ divInd (pairPower p q 1 1)
                  ((B.actualComponentValuationLaw xi c).value m)) -
              PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n
                (pairPower p q 1 1)| ≤
              profileError B.sampleData.n * pairWeight p q 1 1) ∧
          (∀ c p, p ∈ primeBand B.sampleData.n B.sampleData.W →
            |(B.actualComponentValuationLaw xi c).probability.expect
                (fun m ↦ divInd p
                  ((B.actualComponentValuationLaw xi c).value m)) -
              PaperScaleMarkedCell.paperDivisibilityMain
                B.sampleData.n p| ≤
              profileError B.sampleData.n * singleWeight p 1) := by
  intro W hW hsupport Acoef Aphys hAcoef hAphys0
  have hupperOne : ∀ sigma, 1 ≤ I.upper sigma := by
    intro sigma
    exact (hlowerOne sigma).trans (I.lower_lt_upper sigma).le
  have hCmax : 1 ≤ Cmax :=
    (hupperOne .minus).trans (hupperMax .minus)
  obtain ⟨mediumError, hmedium0, hmediumT, hmediumRate,
      Nmedium, hmedium⟩ :=
    exists_boxIndependent_actual_medium_signed_profiles
      Phead I Cmax hupperOne hupperMax Cprom Cbank ledger
        W hW hsupport Acoef hAcoef
  let K := Acoef * PaperStatisticNorm.valuationLogCoefficient Cmax W
  let rhoCell : Cell Head → ℝ := fun c ↦
    PaperScaleMarkedCell.paperCellDensity (Phead c.1)
      (I.lower c.2) (I.upper c.2) / (4 * I.upper c.2)
  let Gcell : Cell Head → ℝ := fun c ↦ Real.exp (2 * K) / rhoCell c
  let Gtotal : ℝ := ∑ c : Cell Head, Gcell c
  let physicalConstant : ℝ :=
    4 * Aphys * Real.log Cmax * Gtotal
  let physicalError : ℕ → ℝ := fun n ↦ physicalConstant / Scale.L n
  let profileError : ℕ → ℝ := fun n ↦ mediumError n + physicalError n
  have hrhoPos (c : Cell Head) : 0 < rhoCell c := by
    dsimp only [rhoCell]
    exact div_pos
      (PaperScaleMarkedCell.paperCellDensity_pos
        (Phead c.1) (I.lower_lt_upper c.2))
      (mul_pos (by norm_num)
        ((I.lower_pos c.2).trans (I.lower_lt_upper c.2)))
  have hGcell0 (c : Cell Head) : 0 ≤ Gcell c := by
    dsimp only [Gcell]
    exact div_nonneg (Real.exp_pos _).le (hrhoPos c).le
  have hGtotal0 : 0 ≤ Gtotal := by
    exact Finset.sum_nonneg fun c _ ↦ hGcell0 c
  have hlogC0 : 0 ≤ Real.log Cmax := Real.log_nonneg hCmax
  have hphysicalConstant0 : 0 ≤ physicalConstant := by
    dsimp only [physicalConstant]
    positivity
  have hL0 (n : ℕ) : 0 ≤ Scale.L n := by
    cases n with
    | zero => norm_num [Scale.L]
    | succ n =>
        exact Real.log_nonneg (by
          exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n)))
  have hphysical0 (n : ℕ) : 0 ≤ physicalError n := by
    exact div_nonneg hphysicalConstant0 (hL0 n)
  have hprofile0 (n : ℕ) : 0 ≤ profileError n :=
    add_nonneg (hmedium0 n) (hphysical0 n)
  have hLTop : Filter.Tendsto Scale.L Filter.atTop Filter.atTop := by
    simpa only [Scale.L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hInvL : Filter.Tendsto (fun n : ℕ ↦ (Scale.L n)⁻¹)
      Filter.atTop (nhds 0) := tendsto_inv_atTop_zero.comp hLTop
  have hphysicalT : Filter.Tendsto physicalError Filter.atTop (nhds 0) := by
    have hraw :=
      (tendsto_const_nhds : Filter.Tendsto
        (fun _n : ℕ ↦ physicalConstant) Filter.atTop
          (nhds physicalConstant)).mul hInvL
    have hzero : Filter.Tendsto
        (fun n : ℕ ↦ physicalConstant * (Scale.L n)⁻¹)
          Filter.atTop (nhds 0) := by
      simpa only [mul_zero] using hraw
    apply hzero.congr'
    filter_upwards with n
    dsimp only [physicalError]
    rw [div_eq_mul_inv]
  have hlogLDivL : Filter.Tendsto
      (fun n : ℕ ↦ Real.log (Scale.L n) / Scale.L n)
        Filter.atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hLTop
  have hphysicalRate : Filter.Tendsto
      (fun n : ℕ ↦ physicalError n * Real.log (Scale.L n))
        Filter.atTop (nhds 0) := by
    have hraw :=
      (tendsto_const_nhds : Filter.Tendsto
        (fun _n : ℕ ↦ physicalConstant) Filter.atTop
          (nhds physicalConstant)).mul hlogLDivL
    have hzero : Filter.Tendsto
        (fun n : ℕ ↦ physicalConstant *
          (Real.log (Scale.L n) / Scale.L n))
          Filter.atTop (nhds 0) := by
      simpa only [mul_zero] using hraw
    apply hzero.congr'
    filter_upwards with n
    dsimp only [physicalError]
    ring
  have hprofileT : Filter.Tendsto profileError Filter.atTop (nhds 0) := by
    simpa only [profileError, add_zero] using hmediumT.add hphysicalT
  have hprofileRate : Filter.Tendsto
      (fun n : ℕ ↦ profileError n * Real.log (Scale.L n))
        Filter.atTop (nhds 0) := by
    simpa only [profileError, add_mul, add_zero] using
      hmediumRate.add hphysicalRate
  have hdensityEvent :=
    Erdos390.Full.GuardSquarefreeErrorRate.eventually_guarded_rawCell_endpoint_density
      Phead I Cprom Cbank ledger
  obtain ⟨Ndensity, hNdensity⟩ := Filter.eventually_atTop.1 hdensityEvent
  have hepsilonT : Filter.Tendsto
      (fun n : ℕ ↦ 8 * (Aphys * Real.log Cmax / Scale.L n))
        Filter.atTop (nhds 0) := by
    have hraw :=
      (tendsto_const_nhds : Filter.Tendsto
        (fun _n : ℕ ↦ 8 * (Aphys * Real.log Cmax)) Filter.atTop
          (nhds (8 * (Aphys * Real.log Cmax)))).mul hInvL
    have hzero : Filter.Tendsto
        (fun n : ℕ ↦ (8 * (Aphys * Real.log Cmax)) *
          (Scale.L n)⁻¹) Filter.atTop (nhds 0) := by
      simpa only [mul_zero] using hraw
    apply hzero.congr'
    filter_upwards with n
    ring
  have hsmallEvent : ∀ᶠ n : ℕ in Filter.atTop,
      8 * (Aphys * Real.log Cmax / Scale.L n) ≤ 1 :=
    hepsilonT.eventually (eventually_le_nhds (by norm_num))
  obtain ⟨Nsmall, hNsmall⟩ := Filter.eventually_atTop.1 hsmallEvent
  let N₀ := max Nmedium (max Ndensity Nsmall)
  refine ⟨profileError, hprofile0, hprofileT, hprofileRate, N₀, ?_⟩
  intro Band _instBand _instBandDec B xi hN hpattern hlo hhi hguards
    heta hphys hBW
  have hNmedium : Nmedium ≤ B.sampleData.n := by
    dsimp only [N₀] at hN
    omega
  have hNdensity' : Ndensity ≤ B.sampleData.n := by
    dsimp only [N₀] at hN
    omega
  have hNsmall' : Nsmall ≤ B.sampleData.n := by
    dsimp only [N₀] at hN
    omega
  have hmediumProfiles := hmedium B xi hNmedium hpattern hlo hhi
    hguards heta hBW
  have hdensityAll := hNdensity B.sampleData.n hNdensity'
  have hsmall : 8 * (Aphys * Real.log Cmax / B.L) ≤ 1 := by
    simpa only [BridgeData.L, Scale.L] using
      hNsmall B.sampleData.n hNsmall'
  have hhiC : ∀ sigma, B.sampleData.hi sigma ≤
      physicalBound Cmax B.sampleData.n := by
    intro sigma
    rw [hhi sigma]
    exact FixedFiniteMixtureFullUniform.physicalBound_mono
      (hupperMax sigma) B.sampleData.n
  have hWBridge : 1 < B.sampleData.W := by simpa only [hBW] using hW
  have hphysicalErrorBound (c : Cell Head) :
      let epsilon := Aphys * Real.log Cmax / B.L
      let G := Real.exp (2 * ((Acoef / B.L) *
        (Real.log (B.sampleData.hi c.2 : ℝ) /
          Real.log (B.sampleData.W : ℝ)))) / rhoCell c
      4 * epsilon * G ≤ physicalError B.sampleData.n := by
    dsimp only
    let exponent := (Acoef / B.L) *
      (Real.log (B.sampleData.hi c.2 : ℝ) /
        Real.log (B.sampleData.W : ℝ))
    let Gactual := Real.exp (2 * exponent) / rhoCell c
    have hexponent : exponent ≤ K := by
      simpa only [exponent, K, hBW] using
        B.mediumFallbackExponent_le c hCmax hWBridge hAcoef (hhiC c.2)
    have hGactual : Gactual ≤ Gcell c := by
      dsimp only [Gactual, Gcell]
      exact div_le_div_of_nonneg_right
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hexponent (by norm_num)))
        (hrhoPos c).le
    have hGcellTotal : Gcell c ≤ Gtotal := by
      exact Finset.single_le_sum (fun d _ ↦ hGcell0 d) (Finset.mem_univ c)
    have hfactor0 : 0 ≤ 4 * (Aphys * Real.log Cmax / B.L) := by
      exact mul_nonneg (by norm_num)
        (div_nonneg (mul_nonneg hAphys0 hlogC0) B.L_pos.le)
    calc
      4 * (Aphys * Real.log Cmax / B.L) * Gactual ≤
          4 * (Aphys * Real.log Cmax / B.L) * Gcell c :=
        mul_le_mul_of_nonneg_left hGactual hfactor0
      _ ≤ 4 * (Aphys * Real.log Cmax / B.L) * Gtotal :=
        mul_le_mul_of_nonneg_left hGcellTotal hfactor0
      _ = physicalError B.sampleData.n := by
        dsimp only [physicalError, physicalConstant, BridgeData.L, Scale.L]
        ring
  have hcoeff (c : Cell Head) :
      mediumError B.sampleData.n +
          4 * (Aphys * Real.log Cmax / B.L) *
            (Real.exp (2 * ((Acoef / B.L) *
              (Real.log (B.sampleData.hi c.2 : ℝ) /
                Real.log (B.sampleData.W : ℝ)))) / rhoCell c) ≤
        profileError B.sampleData.n := by
    dsimp only [profileError]
    exact add_le_add_right (hphysicalErrorBound c) _
  have hlocal (c : Cell Head) := by
    have hdensityC := hdensityAll c
    have hrho : 0 < rhoCell c := hrhoPos c
    have hcard : rhoCell c * (B.sampleData.hi c.2 : ℝ) ≤
        ((B.sampleData.cellFinset c).card : ℝ) := by
      simpa only [rhoCell, StructuredSampleData.cellFinset,
        PaperGuardCensus.rawCell, hpattern, hlo, hhi, hguards] using
          hdensityC.2
    have hKphys : ∀ m : B.sampleData.SampleAt c,
        |B.physicalScore ⟨c, m⟩| ≤ Real.log Cmax := by
      intro m
      exact B.abs_physicalScore_le_log_upperBound I hlowerOne hupperMax
        hlo hhi ⟨c, m⟩
    exact B.actualComponent_squarefree_profiles_of_medium xi c
      hAcoef hWBridge hrho hcard heta hAphys0 hlogC0 hphys hKphys hsmall
      (hmediumProfiles.1 c) (hmediumProfiles.2 c)
  constructor
  · intro c p hp q hq
    exact (hlocal c).1 p hp q hq |>.trans
      (mul_le_mul_of_nonneg_right (hcoeff c)
        (pairWeight_nonneg p q 1 1))
  · intro c p hp
    exact (hlocal c).2 p hp |>.trans
      (mul_le_mul_of_nonneg_right (hcoeff c)
        (singleWeight_nonneg p 1))

private theorem boundedValuationLaw_ext
    {Omega : Type*} [Fintype Omega] {M : ℕ}
    {law₁ law₂ : BoundedValuationLaw Omega M}
    (hprob : law₁.probability = law₂.probability)
    (hvalue : law₁.value = law₂.value) : law₁ = law₂ := by
  cases law₁
  cases law₂
  dsimp only at hprob hvalue
  subst_vars
  rfl

/-- The component mixture just constructed is literally the paper's global
tilted bounded valuation law.  In particular no between-cell covariance is
discarded. -/
theorem sigmaMixture_actualComponentValuationLaw_eq_actualValuationLaw
    [Nonempty Head] (xi : B.ParamSpace) :
    let weight := tiltedSigmaWeight B.baselineCellProbability
      B.guardedCellProbability (B.scaledBridgeScore xi)
    sigmaMixture weight (B.actualComponentValuationLaw xi) =
      B.actualValuationLaw xi := by
  dsimp only
  apply boundedValuationLaw_ext
  · exact congrArg id (B.tiltedLaw_eq_tiltedSigmaMixture xi).symm
  · rfl

/-- Exact actual-law specialization of the signed-profile-to-canonical-row
connector.  The hypotheses are local one- and two-divisor estimates; the
global component weights, their partition functions, and all between-cell
covariance terms are handled by the theorem rather than assumed away. -/
theorem abs_actual_squarefreeSharpRow_sub_arithmeticSharpOperator_le
    [Nonempty Head]
    (xi : B.ParamSpace)
    (cert : Erdos390.Full.PositiveCellTransfer.IntervalCertificate B.partition)
    {Eprofile CKernel : ℝ} (hEprofile : 0 ≤ Eprofile)
    (hn : 1 < B.sampleData.n) (hW : 1 < B.sampleData.W)
    (hpair : ∀ c p, p ∈ primeBand B.sampleData.n B.sampleData.W →
      ∀ q, q ∈ (primeBand B.sampleData.n B.sampleData.W).erase p →
      |(B.actualComponentValuationLaw xi c).probability.expect
          (fun omega ↦ divInd (pairPower p q 1 1)
            ((B.actualComponentValuationLaw xi c).value omega)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n
          (pairPower p q 1 1)| ≤
        Eprofile * pairWeight p q 1 1)
    (hsingle : ∀ c p, p ∈ primeBand B.sampleData.n B.sampleData.W →
      |(B.actualComponentValuationLaw xi c).probability.expect
          (fun omega ↦ divInd p
            ((B.actualComponentValuationLaw xi c).value omega)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n p| ≤
        Eprofile * singleWeight p 1)
    (hKernel : ∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
      |ConditionedPoissonLimit.covarianceKernel
          (tPrime B.sampleData.n p) (tPrime B.sampleData.n p)| ≤ CKernel)
    (q : Band → ℝ) (hq : ∀ j, |q j| ≤ 1) (i : Band) :
    |SquarefreeSharpBandTransfer.squarefreeSharpRow
        (B.actualValuationLaw xi) B.partition q i -
      CompressedArithmeticOperator.arithmeticSharpOperator
        (y B.sampleData.n) cert.lower cert.upper
        B.partition.center q i| ≤
      (4 * PaperPrimePowerChamberError.pairCovarianceScale Eprofile) *
          PrimeSums.bandTReciprocalSum B.sampleData.n B.sampleData.W /
            B.partition.center i +
        2 * Eprofile +
        ((1 / DickmanBasic.rho DickmanBasic.U + 2 * Eprofile) ^ 2 +
            CKernel) * (1 / (B.sampleData.W : ℝ)) := by
  let weight := tiltedSigmaWeight B.baselineCellProbability
    B.guardedCellProbability (B.scaledBridgeScore xi)
  have hraw :=
    SquarefreeReferenceOperatorIdentification.abs_sigmaMixture_squarefreeSharpRow_sub_arithmeticSharpOperator_le
      (P := B.partition) (M := B.sampleEndpoint)
      cert hEprofile weight
      (B.actualComponentValuationLaw xi) hn hW hpair hsingle hKernel q hq i
  have hlaw := B.sigmaMixture_actualComponentValuationLaw_eq_actualValuationLaw xi
  dsimp only at hlaw
  rw [hlaw] at hraw
  simpa only [weight] using hraw

/-- The complete sharp-row error after inserting the moving-low reciprocal
center envelope `1/alpha_i ≤ Calpha log L`. -/
def squarefreeSharpProfileRemainder
    (E : ℕ → ℝ) (Calpha K CKernel : ℝ) (W n : ℕ) : ℝ :=
  (4 * PaperPrimePowerChamberError.pairCovarianceScale (E n)) * K *
      (Calpha * Real.log (Scale.L n)) +
    2 * E n +
    ((1 / DickmanBasic.rho DickmanBasic.U + 2 * E n) ^ 2 + CKernel) *
      (1 / (W : ℝ))

/-- The profile covariance error keeps the same moving-low rate as the
underlying one- and two-divisor profile. -/
theorem tendsto_pairCovarianceScale_mul_logL_zero
    (E : ℕ → ℝ)
    (hE : Filter.Tendsto E Filter.atTop (nhds 0))
    (hERate : Filter.Tendsto
      (fun n : ℕ ↦ E n * Real.log (Scale.L n))
        Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun n : ℕ ↦ PaperPrimePowerChamberError.pairCovarianceScale (E n) *
        Real.log (Scale.L n)) Filter.atTop (nhds 0) := by
  have hSqRate : Filter.Tendsto
      (fun n : ℕ ↦ E n ^ 2 * Real.log (Scale.L n))
        Filter.atTop (nhds 0) := by
    have hraw := hE.mul hERate
    have hzero : Filter.Tendsto
        (fun n : ℕ ↦ E n * (E n * Real.log (Scale.L n)))
          Filter.atTop (nhds 0) := by
      simpa only [mul_zero] using hraw
    apply hzero.congr'
    filter_upwards with n
    ring
  let a : ℝ := 1 + 2 * (1 / DickmanBasic.rho DickmanBasic.U)
  have hlin : Filter.Tendsto
      (fun n : ℕ ↦ a * (E n * Real.log (Scale.L n)))
        Filter.atTop (nhds 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul hERate : Filter.Tendsto
        (fun n : ℕ ↦ a * (E n * Real.log (Scale.L n)))
          Filter.atTop (nhds (a * 0)))
  have hsum := hlin.add hSqRate
  have hzero : Filter.Tendsto
      (fun n : ℕ ↦
        a * (E n * Real.log (Scale.L n)) +
          E n ^ 2 * Real.log (Scale.L n))
        Filter.atTop (nhds 0) := by
    simpa only [add_zero] using hsum
  apply hzero.congr'
  filter_upwards with n
  unfold PaperPrimePowerChamberError.pairCovarianceScale
  dsimp only [a]
  ring

/-- A profile with `E log L → 0` produces a vanishing moving-low row term.
The only surviving term is the explicit diagonal `1/W` correction, which is
selected before the ambient limit. -/
theorem tendsto_squarefreeSharpProfileRemainder
    (E : ℕ → ℝ) (Calpha K CKernel : ℝ) (W : ℕ)
    (hE : Filter.Tendsto E Filter.atTop (nhds 0))
    (hERate : Filter.Tendsto
      (fun n : ℕ ↦ E n * Real.log (Scale.L n))
        Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (squarefreeSharpProfileRemainder E Calpha K CKernel W)
      Filter.atTop
      (nhds (((1 / DickmanBasic.rho DickmanBasic.U) ^ 2 + CKernel) *
        (1 / (W : ℝ)))) := by
  have hcovRate := tendsto_pairCovarianceScale_mul_logL_zero E hE hERate
  have hmoving : Filter.Tendsto
      (fun n : ℕ ↦
        (4 * PaperPrimePowerChamberError.pairCovarianceScale (E n)) * K *
          (Calpha * Real.log (Scale.L n)))
        Filter.atTop (nhds 0) := by
    let c : ℝ := 4 * K * Calpha
    have hraw : Filter.Tendsto
        (fun n : ℕ ↦ c *
          (PaperPrimePowerChamberError.pairCovarianceScale (E n) *
            Real.log (Scale.L n))) Filter.atTop (nhds 0) := by
      simpa only [mul_zero] using
        (tendsto_const_nhds.mul hcovRate : Filter.Tendsto
          (fun n : ℕ ↦ c *
            (PaperPrimePowerChamberError.pairCovarianceScale (E n) *
              Real.log (Scale.L n))) Filter.atTop (nhds (c * 0)))
    apply hraw.congr'
    filter_upwards with n
    dsimp only [c]
    ring
  have hlinear : Filter.Tendsto (fun n : ℕ ↦ 2 * E n)
      Filter.atTop (nhds 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul hE : Filter.Tendsto
        (fun n : ℕ ↦ (2 : ℝ) * E n) Filter.atTop (nhds (2 * 0)))
  let a : ℝ := 1 / DickmanBasic.rho DickmanBasic.U
  have hinside : Filter.Tendsto (fun n : ℕ ↦ a + 2 * E n)
      Filter.atTop (nhds a) := by
    simpa only [add_zero] using tendsto_const_nhds.add hlinear
  have hlast : Filter.Tendsto
      (fun n : ℕ ↦ ((a + 2 * E n) ^ 2 + CKernel) * (1 / (W : ℝ)))
      Filter.atTop (nhds ((a ^ 2 + CKernel) * (1 / (W : ℝ)))) := by
    exact (hinside.pow 2 |>.add tendsto_const_nhds).mul tendsto_const_nhds
  have hsum := (hmoving.add hlinear).add hlast
  simpa only [squarefreeSharpProfileRemainder, a, zero_add] using hsum

/-- Pointwise moving-low specialization of the actual squarefree reference
bound.  This theorem makes the delicate use of `alpha_0` explicit: the only
input is the quantitative envelope `1/alpha_i ≤ Calpha log L`, and no bare
`o(1)` error is accepted. -/
theorem abs_actual_squarefreeSharpRow_sub_arithmetic_le_profileRemainder
    [Nonempty Head]
    (xi : B.ParamSpace)
    (cert : Erdos390.Full.PositiveCellTransfer.IntervalCertificate B.partition)
    {Eprofile Calpha K CKernel : ℝ}
    (hEprofile : 0 ≤ Eprofile)
    (hW : 1 < B.sampleData.W)
    (hpair : ∀ c p, p ∈ primeBand B.sampleData.n B.sampleData.W →
      ∀ q, q ∈ (primeBand B.sampleData.n B.sampleData.W).erase p →
      |(B.actualComponentValuationLaw xi c).probability.expect
          (fun omega ↦ divInd (pairPower p q 1 1)
            ((B.actualComponentValuationLaw xi c).value omega)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n
          (pairPower p q 1 1)| ≤
        Eprofile * pairWeight p q 1 1)
    (hsingle : ∀ c p, p ∈ primeBand B.sampleData.n B.sampleData.W →
      |(B.actualComponentValuationLaw xi c).probability.expect
          (fun omega ↦ divInd p
            ((B.actualComponentValuationLaw xi c).value omega)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n p| ≤
        Eprofile * singleWeight p 1)
    (hKernel : ∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
      |ConditionedPoissonLimit.covarianceKernel
          (tPrime B.sampleData.n p) (tPrime B.sampleData.n p)| ≤ CKernel)
    (hBandT : PrimeSums.bandTReciprocalSum
      B.sampleData.n B.sampleData.W ≤ K)
    (hcenterInv : ∀ i : Band,
      1 / B.partition.center i ≤
        Calpha * Real.log (Scale.L B.sampleData.n))
    (q : Band → ℝ) (hq : ∀ j, |q j| ≤ 1) (i : Band) :
    |SquarefreeSharpBandTransfer.squarefreeSharpRow
        (B.actualValuationLaw xi) B.partition q i -
      CompressedArithmeticOperator.arithmeticSharpOperator
        (y B.sampleData.n) cert.lower cert.upper
        B.partition.center q i| ≤
      squarefreeSharpProfileRemainder
        (fun _n ↦ Eprofile) Calpha K CKernel
          B.sampleData.W B.sampleData.n := by
  have hbase := B.abs_actual_squarefreeSharpRow_sub_arithmeticSharpOperator_le
    xi cert hEprofile B.n_gt_one
      hW hpair hsingle hKernel q hq i
  have hcov0 : 0 ≤
      4 * PaperPrimePowerChamberError.pairCovarianceScale Eprofile :=
    mul_nonneg (by norm_num)
      (PaperPrimePowerChamberError.pairCovarianceScale_nonneg hEprofile)
  have hBandT0 : 0 ≤ PrimeSums.bandTReciprocalSum
      B.sampleData.n B.sampleData.W := by
    unfold PrimeSums.bandTReciprocalSum
    apply Finset.sum_nonneg
    intro p hp
    exact div_nonneg (B.bandPrime_tPrime_pos ⟨p, hp⟩).le (by positivity)
  have hK0' : 0 ≤ K := hBandT0.trans hBandT
  have hcenterPos : 0 < B.partition.center i :=
    B.partition.center_pos B.n_gt_one i
  have hmoving :
      (4 * PaperPrimePowerChamberError.pairCovarianceScale Eprofile) *
          PrimeSums.bandTReciprocalSum
            B.sampleData.n B.sampleData.W / B.partition.center i ≤
        (4 * PaperPrimePowerChamberError.pairCovarianceScale Eprofile) * K *
          (Calpha * Real.log (Scale.L B.sampleData.n)) := by
    calc
      (4 * PaperPrimePowerChamberError.pairCovarianceScale Eprofile) *
            PrimeSums.bandTReciprocalSum
              B.sampleData.n B.sampleData.W / B.partition.center i =
          (4 * PaperPrimePowerChamberError.pairCovarianceScale Eprofile) *
            PrimeSums.bandTReciprocalSum
              B.sampleData.n B.sampleData.W *
                (1 / B.partition.center i) := by ring
      _ ≤ (4 * PaperPrimePowerChamberError.pairCovarianceScale Eprofile) * K *
            (1 / B.partition.center i) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hBandT hcov0)
          (one_div_nonneg.mpr hcenterPos.le)
      _ ≤ (4 * PaperPrimePowerChamberError.pairCovarianceScale Eprofile) * K *
            (Calpha * Real.log (Scale.L B.sampleData.n)) := by
        exact mul_le_mul_of_nonneg_left (hcenterInv i)
          (mul_nonneg hcov0 hK0')
  unfold squarefreeSharpProfileRemainder
  exact hbase.trans (by linarith [hmoving])

/-- Box-independent, unconditional actual-law squarefree reference bound.
The profile hypotheses of
`abs_actual_squarefreeSharpRow_sub_arithmeticSharpOperator_le` are discharged
from the literal guarded cells, and the single exported error has the sharp
moving-low rate `E(n) log L(n) → 0`. -/
theorem exists_boxIndependent_actual_squarefreeSharp_reference_bound
    [Nonempty Head]
    (Phead : Head → HeadPattern.Pattern)
    (I : PaperGuardCensus.PhysicalIntervals) (Cmax : ℝ)
    (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
    (hupperMax : ∀ sigma, I.upper sigma ≤ Cmax)
    (Cprom Cbank : ℕ)
    (ledger : ∀ n, PaperGuardCensus.Ledger n Cprom Cbank) :
    ∀ W : ℕ, 1 < W → (∀ h, (Phead h).modulus ≤ W) →
    ∀ Acoef Aphys : ℝ, 0 ≤ Acoef → 0 ≤ Aphys →
    ∃ profileError : ℕ → ℝ,
      (∀ n, 0 ≤ profileError n) ∧
      Filter.Tendsto profileError Filter.atTop (nhds 0) ∧
      Filter.Tendsto (fun n : ℕ ↦ profileError n * Real.log (Scale.L n))
        Filter.atTop (nhds 0) ∧
      ∃ N₀ : ℕ,
        ∀ {Band : Type*} [Fintype Band] [DecidableEq Band]
          (B : BridgeData Head Band) (xi : B.ParamSpace)
          (cert : Erdos390.Full.PositiveCellTransfer.IntervalCertificate
            B.partition),
          N₀ ≤ B.sampleData.n →
          B.sampleData.pattern = Phead →
          (∀ sigma, B.sampleData.lo sigma =
            physicalBound (I.lower sigma) B.sampleData.n) →
          (∀ sigma, B.sampleData.hi sigma =
            physicalBound (I.upper sigma) B.sampleData.n) →
          B.sampleData.guards = (ledger B.sampleData.n).guards →
          (∀ p : BandPrime B.sampleData.n B.sampleData.W,
            |B.effectivePrimeCoefficient xi p| ≤ Acoef) →
          |xi MomentCoord.physical| ≤ Aphys →
          B.sampleData.W = W →
          ∀ {CKernel : ℝ},
          (∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
            |ConditionedPoissonLimit.covarianceKernel
                (tPrime B.sampleData.n p) (tPrime B.sampleData.n p)| ≤
              CKernel) →
          ∀ (q : Band → ℝ), (∀ j, |q j| ≤ 1) → ∀ i : Band,
          |SquarefreeSharpBandTransfer.squarefreeSharpRow
              (B.actualValuationLaw xi) B.partition q i -
            CompressedArithmeticOperator.arithmeticSharpOperator
              (y B.sampleData.n) cert.lower cert.upper
              B.partition.center q i| ≤
            (4 * PaperPrimePowerChamberError.pairCovarianceScale
                (profileError B.sampleData.n)) *
                PrimeSums.bandTReciprocalSum
                  B.sampleData.n B.sampleData.W /
                  B.partition.center i +
              2 * profileError B.sampleData.n +
              ((1 / DickmanBasic.rho DickmanBasic.U +
                    2 * profileError B.sampleData.n) ^ 2 + CKernel) *
                (1 / (B.sampleData.W : ℝ)) := by
  intro W hW hmod Acoef Aphys hAcoef hAphys
  obtain ⟨profileError, herror0, herrorT, herrorRate, N₀, hprofiles⟩ :=
    exists_boxIndependent_actual_component_signed_profiles
      Phead I Cmax hlowerOne hupperMax Cprom Cbank ledger
        W hW
          (fun h p hp ↦
            PaperPrimePowerAuxiliaryPrime.headPrime_le_cutoff_of_modulus_le
              (Phead h) (hmod h) p hp)
          Acoef Aphys hAcoef hAphys
  refine ⟨profileError, herror0, herrorT, herrorRate, N₀, ?_⟩
  intro Band _instBand _instBandDec B xi cert hN hpattern hlo hhi
    hguards heta hphysical hBW CKernel hKernel q hq i
  have hcomponent := hprofiles B xi hN hpattern hlo hhi hguards heta
    hphysical hBW
  exact B.abs_actual_squarefreeSharpRow_sub_arithmeticSharpOperator_le
    xi cert (herror0 B.sampleData.n) B.n_gt_one
      (by simpa only [hBW] using hW) hcomponent.1 hcomponent.2
      hKernel q hq i

/-! ### Exact finite-dimensional attachment to the arithmetic inverse -/

private theorem squarefreeSharpRow_add
    [Nonempty Head]
    (xi : B.ParamSpace) (q r : Band → ℝ) (i : Band) :
    SquarefreeSharpBandTransfer.squarefreeSharpRow
        (B.actualValuationLaw xi) B.partition (q + r) i =
      SquarefreeSharpBandTransfer.squarefreeSharpRow
          (B.actualValuationLaw xi) B.partition q i +
        SquarefreeSharpBandTransfer.squarefreeSharpRow
          (B.actualValuationLaw xi) B.partition r i := by
  unfold SquarefreeSharpBandTransfer.squarefreeSharpRow
    SquarefreeSharpBandTransfer.squarefreeBandRow
  simp only [Pi.add_apply, mul_add, add_mul]
  have hinner (p : ArithmeticBandGeometry.BandPrime
      B.sampleData.n B.sampleData.W) :
      (∑ s : ArithmeticBandGeometry.BandPrime
          B.sampleData.n B.sampleData.W,
        (B.partition.center (B.partition.band s) * q (B.partition.band s) *
            (B.actualValuationLaw xi).covII p.1 s.1 +
          B.partition.center (B.partition.band s) * r (B.partition.band s) *
            (B.actualValuationLaw xi).covII p.1 s.1)) =
        (∑ s : ArithmeticBandGeometry.BandPrime
            B.sampleData.n B.sampleData.W,
          B.partition.center (B.partition.band s) * q (B.partition.band s) *
            (B.actualValuationLaw xi).covII p.1 s.1) +
        ∑ s : ArithmeticBandGeometry.BandPrime
            B.sampleData.n B.sampleData.W,
          B.partition.center (B.partition.band s) * r (B.partition.band s) *
            (B.actualValuationLaw xi).covII p.1 s.1 := by
    exact Finset.sum_add_distrib
  have hsum :
      (∑ p ∈ B.partition.data.fiber i,
        ∑ s : ArithmeticBandGeometry.BandPrime
            B.sampleData.n B.sampleData.W,
          (B.partition.center (B.partition.band s) * q (B.partition.band s) *
              (B.actualValuationLaw xi).covII p.1 s.1 +
            B.partition.center (B.partition.band s) * r (B.partition.band s) *
              (B.actualValuationLaw xi).covII p.1 s.1)) =
        (∑ p ∈ B.partition.data.fiber i,
          ∑ s : ArithmeticBandGeometry.BandPrime
              B.sampleData.n B.sampleData.W,
            B.partition.center (B.partition.band s) * q (B.partition.band s) *
              (B.actualValuationLaw xi).covII p.1 s.1) +
        ∑ p ∈ B.partition.data.fiber i,
          ∑ s : ArithmeticBandGeometry.BandPrime
              B.sampleData.n B.sampleData.W,
            B.partition.center (B.partition.band s) * r (B.partition.band s) *
              (B.actualValuationLaw xi).covII p.1 s.1 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _hp
    exact hinner p
  rw [hsum]
  ring

private theorem squarefreeSharpRow_smul
    [Nonempty Head]
    (xi : B.ParamSpace) (c : ℝ) (q : Band → ℝ) (i : Band) :
    SquarefreeSharpBandTransfer.squarefreeSharpRow
        (B.actualValuationLaw xi) B.partition (c • q) i =
      c * SquarefreeSharpBandTransfer.squarefreeSharpRow
        (B.actualValuationLaw xi) B.partition q i := by
  unfold SquarefreeSharpBandTransfer.squarefreeSharpRow
    SquarefreeSharpBandTransfer.squarefreeBandRow
  simp only [Pi.smul_apply, smul_eq_mul]
  have hinner (p : ArithmeticBandGeometry.BandPrime
      B.sampleData.n B.sampleData.W) :
      (∑ r : ArithmeticBandGeometry.BandPrime
          B.sampleData.n B.sampleData.W,
        B.partition.center (B.partition.band r) *
            (c * q (B.partition.band r)) *
              (B.actualValuationLaw xi).covII p.1 r.1) =
        c * (∑ r : ArithmeticBandGeometry.BandPrime
          B.sampleData.n B.sampleData.W,
          B.partition.center (B.partition.band r) *
            q (B.partition.band r) *
              (B.actualValuationLaw xi).covII p.1 r.1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _hr
    ring
  simp_rw [hinner]
  rw [← Finset.mul_sum]
  ring

/-- The exact sharp gauge weight has positive total mass.  This is a finite
arithmetic fact: every harmonic mass and every arithmetic center is positive,
and `lowBand` supplies a witness to the nonempty sum. -/
theorem actualSharpWeightTotal_pos :
    0 < MovingLowGaugeTransfer.sharpWeightTotal
      B.partition.mass B.partition.center := by
  unfold MovingLowGaugeTransfer.sharpWeightTotal
    MovingLowGaugeTransfer.sharpWeight
  apply Finset.sum_pos
  · intro j _hj
    exact mul_pos (B.partition.data.mass_pos j)
      (sq_pos_of_pos (B.partition.center_pos B.n_gt_one j))
  · exact ⟨B.lowBand, Finset.mem_univ _⟩

/-- The literal actual squarefree covariance operator, projected to the exact
finite arithmetic sharp gauge.  No reference kernel or asymptotic estimate
occurs in this definition. -/
def actualSquarefreeProjectedLinearMap
    [Nonempty Head] (xi : B.ParamSpace) :
    PaperWeightedInverseExport.SharpGaugeSpace
        B.partition.mass B.partition.center →ₗ[ℝ]
      PaperWeightedInverseExport.SharpGaugeSpace
        B.partition.mass B.partition.center where
  toFun q :=
    ⟨FiniteGraphQuotientInverse.meanProjection
        (MovingLowGaugeTransfer.sharpWeight
          B.partition.mass B.partition.center)
        (fun i ↦ SquarefreeSharpBandTransfer.squarefreeSharpRow
          (B.actualValuationLaw xi) B.partition q.1 i),
      FiniteGraphStableInverse.weighted_sum_meanProjection
        (MovingLowGaugeTransfer.sharpWeight
          B.partition.mass B.partition.center)
        (fun i ↦ SquarefreeSharpBandTransfer.squarefreeSharpRow
          (B.actualValuationLaw xi) B.partition q.1 i)
        (ne_of_gt (actualSharpWeightTotal_pos B))⟩
  map_add' q r := by
    apply Subtype.ext
    funext i
    change FiniteGraphQuotientInverse.meanProjection
        (MovingLowGaugeTransfer.sharpWeight
          B.partition.mass B.partition.center)
        (fun j ↦ SquarefreeSharpBandTransfer.squarefreeSharpRow
          (B.actualValuationLaw xi) B.partition (q.1 + r.1) j) i = _
    rw [show (fun j ↦ SquarefreeSharpBandTransfer.squarefreeSharpRow
        (B.actualValuationLaw xi) B.partition (q.1 + r.1) j) =
        (fun j ↦ SquarefreeSharpBandTransfer.squarefreeSharpRow
          (B.actualValuationLaw xi) B.partition q.1 j) +
        (fun j ↦ SquarefreeSharpBandTransfer.squarefreeSharpRow
          (B.actualValuationLaw xi) B.partition r.1 j) by
      funext j
      exact B.squarefreeSharpRow_add xi q.1 r.1 j]
    exact FiniteGraphStableInverse.meanProjection_add
      (MovingLowGaugeTransfer.sharpWeight
        B.partition.mass B.partition.center) _ _ i
  map_smul' c q := by
    apply Subtype.ext
    funext i
    change FiniteGraphQuotientInverse.meanProjection
        (MovingLowGaugeTransfer.sharpWeight
          B.partition.mass B.partition.center)
        (fun j ↦ SquarefreeSharpBandTransfer.squarefreeSharpRow
          (B.actualValuationLaw xi) B.partition (c • q.1) j) i = _
    rw [show (fun j ↦ SquarefreeSharpBandTransfer.squarefreeSharpRow
        (B.actualValuationLaw xi) B.partition (c • q.1) j) =
        c • (fun j ↦ SquarefreeSharpBandTransfer.squarefreeSharpRow
          (B.actualValuationLaw xi) B.partition q.1 j) by
      funext j
      exact B.squarefreeSharpRow_smul xi c q.1 j]
    exact FiniteGraphStableInverse.meanProjection_smul
      (MovingLowGaugeTransfer.sharpWeight
        B.partition.mass B.partition.center) c _ i

def actualSquarefreeProjectedCLM
    [Nonempty Head] (xi : B.ParamSpace) :
    PaperWeightedInverseExport.SharpGaugeSpace
        B.partition.mass B.partition.center →L[ℝ]
      PaperWeightedInverseExport.SharpGaugeSpace
        B.partition.mass B.partition.center :=
  (B.actualSquarefreeProjectedLinearMap xi).toContinuousLinearMap

/-- A unit sharp-row comparison gives an operator-norm comparison after the
exact arithmetic gauge projection.  The factor two is exactly the norm of
subtracting the weighted mean; it is independent of the moving-low mass and
of the number of bands. -/
theorem actualSquarefreeProjectedCLM_sub_arithmetic_le
    [Nonempty Head]
    (xi : B.ParamSpace)
    (cert : Erdos390.Full.PositiveCellTransfer.IntervalCertificate B.partition)
    {r : ℝ} (hr : 0 ≤ r)
    (hrow : ∀ (q : Band → ℝ), (∀ j, |q j| ≤ 1) → ∀ i : Band,
      |SquarefreeSharpBandTransfer.squarefreeSharpRow
          (B.actualValuationLaw xi) B.partition q i -
        CompressedArithmeticOperator.arithmeticSharpOperator
          (y B.sampleData.n) cert.lower cert.upper
            B.partition.center q i| ≤ r)
    (q : PaperWeightedInverseExport.SharpGaugeSpace
      B.partition.mass B.partition.center) :
    ‖(B.actualSquarefreeProjectedCLM xi -
        ArithmeticGaugeStableInverse.projectedSharpCLM
          (CompressedArithmeticOperator.arithmeticDiagonal
            (y B.sampleData.n) cert.lower cert.upper)
          (CompressedArithmeticOperator.arithmeticKernel
            (y B.sampleData.n) cert.lower cert.upper)
          B.partition.center
          (MovingLowGaugeTransfer.sharpWeight
            B.partition.mass B.partition.center)
          (ne_of_gt (actualSharpWeightTotal_pos B))) q‖ ≤
      (2 * r) * ‖q‖ := by
  let omega := MovingLowGaugeTransfer.sharpWeight
    B.partition.mass B.partition.center
  let actualRow : (Band → ℝ) → Band → ℝ := fun b i ↦
    SquarefreeSharpBandTransfer.squarefreeSharpRow
      (B.actualValuationLaw xi) B.partition b i
  let referenceRow : (Band → ℝ) → Band → ℝ := fun b i ↦
    CompressedArithmeticOperator.arithmeticSharpOperator
      (y B.sampleData.n) cert.lower cert.upper B.partition.center b i
  have hraw (i : Band) :
      |actualRow q.1 i - referenceRow q.1 i| ≤ r * ‖q‖ := by
    by_cases hqzero : ‖q‖ = 0
    · have hq0 : q = 0 := norm_eq_zero.mp hqzero
      subst q
      have ha : actualRow (0 : Band → ℝ) i = 0 := by
        simpa only [actualRow, zero_smul, zero_mul] using
          B.squarefreeSharpRow_smul xi 0 (0 : Band → ℝ) i
      have href : referenceRow (0 : Band → ℝ) i = 0 := by
        simpa only [referenceRow, zero_smul, zero_mul] using
          ArithmeticGaugeStableInverse.sharpOperator_smul
            (CompressedArithmeticOperator.arithmeticDiagonal
              (y B.sampleData.n) cert.lower cert.upper)
            (CompressedArithmeticOperator.arithmeticKernel
              (y B.sampleData.n) cert.lower cert.upper)
            B.partition.center (0 : Band → ℝ) 0 i
      have hcoe :
          (((0 : PaperWeightedInverseExport.SharpGaugeSpace
            B.partition.mass B.partition.center) :
              PaperWeightedInverseExport.SharpGaugeSpace
                B.partition.mass B.partition.center) : Band → ℝ) = 0 := rfl
      rw [hcoe, ha, href, norm_zero, mul_zero]
      norm_num
    · have hqpos : 0 < ‖q‖ := lt_of_le_of_ne (norm_nonneg q) (Ne.symm hqzero)
      let q0 : Band → ℝ := fun j ↦ q.1 j / ‖q‖
      have hq0unit (j : Band) : |q0 j| ≤ 1 := by
        have hj : |q.1 j| ≤ ‖q‖ := by
          rw [← Real.norm_eq_abs]
          exact norm_le_pi_norm q.1 j
        dsimp only [q0]
        rw [abs_div, abs_of_pos hqpos]
        exact (div_le_one hqpos).2 hj
      have hunit := hrow q0 hq0unit i
      have hqEq : q.1 = ‖q‖ • q0 := by
        funext j
        dsimp only [q0]
        simp only [Pi.smul_apply, smul_eq_mul]
        field_simp [hqzero]
      have hactual : actualRow q.1 i = ‖q‖ * actualRow q0 i := by
        rw [hqEq]
        exact B.squarefreeSharpRow_smul xi ‖q‖ q0 i
      have hreference : referenceRow q.1 i = ‖q‖ * referenceRow q0 i := by
        rw [hqEq]
        exact ArithmeticGaugeStableInverse.sharpOperator_smul
          (CompressedArithmeticOperator.arithmeticDiagonal
            (y B.sampleData.n) cert.lower cert.upper)
          (CompressedArithmeticOperator.arithmeticKernel
            (y B.sampleData.n) cert.lower cert.upper)
          B.partition.center q0 ‖q‖ i
      rw [hactual, hreference, ← mul_sub, abs_mul, abs_of_pos hqpos]
      exact (mul_le_mul_of_nonneg_left hunit hqpos.le).trans_eq
        (mul_comm ‖q‖ r)
  have hprojected (i : Band) :
      |FiniteGraphQuotientInverse.meanProjection omega
          (actualRow q.1) i -
        FiniteGraphQuotientInverse.meanProjection omega
          (referenceRow q.1) i| ≤ 2 * (r * ‖q‖) :=
    CompressedArithmeticOperator.abs_meanProjection_sub_le omega
      (actualRow q.1) (referenceRow q.1) (r * ‖q‖)
      (fun i ↦ MovingLowGaugeTransfer.sharpWeight_nonneg_of_mass_nonneg
        B.partition.mass B.partition.center
          (fun j ↦ (B.partition.data.mass_pos j).le) i)
      (actualSharpWeightTotal_pos B) hraw i
  have hnonneg : 0 ≤ (2 * r) * ‖q‖ := by positivity
  change ‖((B.actualSquarefreeProjectedCLM xi -
        ArithmeticGaugeStableInverse.projectedSharpCLM
          (CompressedArithmeticOperator.arithmeticDiagonal
            (y B.sampleData.n) cert.lower cert.upper)
          (CompressedArithmeticOperator.arithmeticKernel
            (y B.sampleData.n) cert.lower cert.upper)
          B.partition.center omega
          (ne_of_gt (actualSharpWeightTotal_pos B))) q :
      PaperWeightedInverseExport.SharpGaugeSpace
        B.partition.mass B.partition.center)‖ ≤ (2 * r) * ‖q‖
  change ‖(((B.actualSquarefreeProjectedCLM xi -
        ArithmeticGaugeStableInverse.projectedSharpCLM
          (CompressedArithmeticOperator.arithmeticDiagonal
            (y B.sampleData.n) cert.lower cert.upper)
          (CompressedArithmeticOperator.arithmeticKernel
            (y B.sampleData.n) cert.lower cert.upper)
          B.partition.center omega
          (ne_of_gt (actualSharpWeightTotal_pos B))) q :
      PaperWeightedInverseExport.SharpGaugeSpace
        B.partition.mass B.partition.center) : Band → ℝ)‖ ≤
      (2 * r) * ‖q‖
  rw [pi_norm_le_iff_of_nonneg hnonneg]
  intro i
  rw [Real.norm_eq_abs]
  exact hprojected i |>.trans_eq (by ring)

/-- A proved arithmetic-reference inverse and the proved unit row comparison
produce an inverse for the literal actual squarefree projected operator.
Invertibility of the perturbed operator is a conclusion, not an input. -/
theorem exists_actualSquarefreeProjectedEquiv_of_reference
    [Nonempty Head]
    (xi : B.ParamSpace)
    (cert : Erdos390.Full.PositiveCellTransfer.IntervalCertificate B.partition)
    (referenceEquiv :
      PaperWeightedInverseExport.SharpGaugeSpace
          B.partition.mass B.partition.center ≃L[ℝ]
        PaperWeightedInverseExport.SharpGaugeSpace
          B.partition.mass B.partition.center)
    (hreference : ∀ q, referenceEquiv q =
      ArithmeticGaugeStableInverse.projectedSharpCLM
        (CompressedArithmeticOperator.arithmeticDiagonal
          (y B.sampleData.n) cert.lower cert.upper)
        (CompressedArithmeticOperator.arithmeticKernel
          (y B.sampleData.n) cert.lower cert.upper)
        B.partition.center
        (MovingLowGaugeTransfer.sharpWeight
          B.partition.mass B.partition.center)
        (ne_of_gt (actualSharpWeightTotal_pos B)) q)
    {C r : ℝ} (hC : 0 ≤ C) (hr : 0 ≤ r)
    (hinv : ∀ v, ‖referenceEquiv.symm v‖ ≤ C * ‖v‖)
    (hsmall : C * (2 * r) < 1)
    (hrow : ∀ (q : Band → ℝ), (∀ j, |q j| ≤ 1) → ∀ i : Band,
      |SquarefreeSharpBandTransfer.squarefreeSharpRow
          (B.actualValuationLaw xi) B.partition q i -
        CompressedArithmeticOperator.arithmeticSharpOperator
          (y B.sampleData.n) cert.lower cert.upper
            B.partition.center q i| ≤ r) :
    ∃ actualEquiv :
      PaperWeightedInverseExport.SharpGaugeSpace
          B.partition.mass B.partition.center ≃L[ℝ]
        PaperWeightedInverseExport.SharpGaugeSpace
          B.partition.mass B.partition.center,
      (∀ q, actualEquiv q = B.actualSquarefreeProjectedCLM xi q) ∧
      ∀ v, ‖actualEquiv.symm v‖ ≤
        (C / (1 - C * (2 * r))) * ‖v‖ := by
  let A := ArithmeticGaugeStableInverse.projectedSharpCLM
    (CompressedArithmeticOperator.arithmeticDiagonal
      (y B.sampleData.n) cert.lower cert.upper)
    (CompressedArithmeticOperator.arithmeticKernel
      (y B.sampleData.n) cert.lower cert.upper)
    B.partition.center
    (MovingLowGaugeTransfer.sharpWeight
      B.partition.mass B.partition.center)
    (ne_of_gt (actualSharpWeightTotal_pos B))
  let Ainv : PaperWeightedInverseExport.SharpGaugeSpace
      B.partition.mass B.partition.center →L[ℝ]
      PaperWeightedInverseExport.SharpGaugeSpace
        B.partition.mass B.partition.center := referenceEquiv.symm
  let E := B.actualSquarefreeProjectedCLM xi - A
  have hleft (q : PaperWeightedInverseExport.SharpGaugeSpace
      B.partition.mass B.partition.center) : Ainv (A q) = q := by
    dsimp only [Ainv, A]
    rw [← hreference q]
    exact referenceEquiv.symm_apply_apply q
  have hinv' (v : PaperWeightedInverseExport.SharpGaugeSpace
      B.partition.mass B.partition.center) : ‖Ainv v‖ ≤ C * ‖v‖ := hinv v
  have herror (q : PaperWeightedInverseExport.SharpGaugeSpace
      B.partition.mass B.partition.center) :
      ‖E q‖ ≤ (2 * r) * ‖q‖ := by
    dsimp only [E, A]
    exact B.actualSquarefreeProjectedCLM_sub_arithmetic_le
      xi cert hr hrow q
  let actualEquiv := StableInverse.perturbedEquiv
    A Ainv E C (2 * r) hC hsmall hleft hinv' herror
  refine ⟨actualEquiv, ?_, ?_⟩
  · intro q
    rw [StableInverse.perturbedEquiv_apply]
    dsimp only [actualEquiv, E]
    simp only [add_sub_cancel]
  · intro v
    exact StableInverse.perturbed_inverse_bound
      A Ainv E C (2 * r) hC hsmall hleft hinv' herror v

private theorem fullSharpRow_add
    [Nonempty Head]
    (xi : B.ParamSpace) (q r : Band → ℝ) (i : Band) :
    PrimePowerSharpBandTransfer.fullSharpRow
        (B.actualValuationLaw xi) B.partition (q + r) i =
      PrimePowerSharpBandTransfer.fullSharpRow
          (B.actualValuationLaw xi) B.partition q i +
        PrimePowerSharpBandTransfer.fullSharpRow
          (B.actualValuationLaw xi) B.partition r i := by
  unfold PrimePowerSharpBandTransfer.fullSharpRow
    PrimePowerSharpBandTransfer.fullBandRow
  simp only [Pi.add_apply]
  have hinner (p : ArithmeticBandGeometry.BandPrime
      B.sampleData.n B.sampleData.W) :
      (∑ s : ArithmeticBandGeometry.BandPrime
          B.sampleData.n B.sampleData.W,
        B.partition.center (B.partition.band s) *
            (q (B.partition.band s) + r (B.partition.band s)) *
              (B.actualValuationLaw xi).covVV p.1 s.1) =
        (∑ s : ArithmeticBandGeometry.BandPrime
            B.sampleData.n B.sampleData.W,
          B.partition.center (B.partition.band s) * q (B.partition.band s) *
            (B.actualValuationLaw xi).covVV p.1 s.1) +
        ∑ s : ArithmeticBandGeometry.BandPrime
            B.sampleData.n B.sampleData.W,
          B.partition.center (B.partition.band s) * r (B.partition.band s) *
            (B.actualValuationLaw xi).covVV p.1 s.1 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s _hs
    ring
  simp_rw [hinner]
  rw [Finset.sum_add_distrib]
  ring

private theorem fullSharpRow_smul
    [Nonempty Head]
    (xi : B.ParamSpace) (c : ℝ) (q : Band → ℝ) (i : Band) :
    PrimePowerSharpBandTransfer.fullSharpRow
        (B.actualValuationLaw xi) B.partition (c • q) i =
      c * PrimePowerSharpBandTransfer.fullSharpRow
        (B.actualValuationLaw xi) B.partition q i := by
  unfold PrimePowerSharpBandTransfer.fullSharpRow
    PrimePowerSharpBandTransfer.fullBandRow
  simp only [Pi.smul_apply, smul_eq_mul]
  have hinner (p : ArithmeticBandGeometry.BandPrime
      B.sampleData.n B.sampleData.W) :
      (∑ s : ArithmeticBandGeometry.BandPrime
          B.sampleData.n B.sampleData.W,
        B.partition.center (B.partition.band s) *
            (c * q (B.partition.band s)) *
              (B.actualValuationLaw xi).covVV p.1 s.1) =
        c * (∑ s : ArithmeticBandGeometry.BandPrime
          B.sampleData.n B.sampleData.W,
          B.partition.center (B.partition.band s) *
            q (B.partition.band s) *
              (B.actualValuationLaw xi).covVV p.1 s.1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _hs
    ring
  simp_rw [hinner]
  rw [← Finset.mul_sum]
  ring

/-- The literal full-valuation covariance operator, projected to the same
finite arithmetic sharp gauge as the squarefree operator. -/
def actualFullProjectedLinearMap
    [Nonempty Head] (xi : B.ParamSpace) :
    PaperWeightedInverseExport.SharpGaugeSpace
        B.partition.mass B.partition.center →ₗ[ℝ]
      PaperWeightedInverseExport.SharpGaugeSpace
        B.partition.mass B.partition.center where
  toFun q :=
    ⟨FiniteGraphQuotientInverse.meanProjection
        (MovingLowGaugeTransfer.sharpWeight
          B.partition.mass B.partition.center)
        (fun i ↦ PrimePowerSharpBandTransfer.fullSharpRow
          (B.actualValuationLaw xi) B.partition q.1 i),
      FiniteGraphStableInverse.weighted_sum_meanProjection
        (MovingLowGaugeTransfer.sharpWeight
          B.partition.mass B.partition.center)
        (fun i ↦ PrimePowerSharpBandTransfer.fullSharpRow
          (B.actualValuationLaw xi) B.partition q.1 i)
        (ne_of_gt (actualSharpWeightTotal_pos B))⟩
  map_add' q r := by
    apply Subtype.ext
    funext i
    change FiniteGraphQuotientInverse.meanProjection
        (MovingLowGaugeTransfer.sharpWeight
          B.partition.mass B.partition.center)
        (fun j ↦ PrimePowerSharpBandTransfer.fullSharpRow
          (B.actualValuationLaw xi) B.partition (q.1 + r.1) j) i = _
    rw [show (fun j ↦ PrimePowerSharpBandTransfer.fullSharpRow
        (B.actualValuationLaw xi) B.partition (q.1 + r.1) j) =
        (fun j ↦ PrimePowerSharpBandTransfer.fullSharpRow
          (B.actualValuationLaw xi) B.partition q.1 j) +
        (fun j ↦ PrimePowerSharpBandTransfer.fullSharpRow
          (B.actualValuationLaw xi) B.partition r.1 j) by
      funext j
      exact B.fullSharpRow_add xi q.1 r.1 j]
    exact FiniteGraphStableInverse.meanProjection_add
      (MovingLowGaugeTransfer.sharpWeight
        B.partition.mass B.partition.center) _ _ i
  map_smul' c q := by
    apply Subtype.ext
    funext i
    change FiniteGraphQuotientInverse.meanProjection
        (MovingLowGaugeTransfer.sharpWeight
          B.partition.mass B.partition.center)
        (fun j ↦ PrimePowerSharpBandTransfer.fullSharpRow
          (B.actualValuationLaw xi) B.partition (c • q.1) j) i = _
    rw [show (fun j ↦ PrimePowerSharpBandTransfer.fullSharpRow
        (B.actualValuationLaw xi) B.partition (c • q.1) j) =
        c • (fun j ↦ PrimePowerSharpBandTransfer.fullSharpRow
          (B.actualValuationLaw xi) B.partition q.1 j) by
      funext j
      exact B.fullSharpRow_smul xi c q.1 j]
    exact FiniteGraphStableInverse.meanProjection_smul
      (MovingLowGaugeTransfer.sharpWeight
        B.partition.mass B.partition.center) c _ i

def actualFullProjectedCLM
    [Nonempty Head] (xi : B.ParamSpace) :
    PaperWeightedInverseExport.SharpGaugeSpace
        B.partition.mass B.partition.center →L[ℝ]
      PaperWeightedInverseExport.SharpGaugeSpace
        B.partition.mass B.partition.center :=
  (B.actualFullProjectedLinearMap xi).toContinuousLinearMap

/-- Lemma 7.5's literal prime-power transfer controls the projected
full-valuation/squarefree difference.  The displayed row budget retains the
only moving-low loss, `epsilon / center i`; no additive `o(1)` is substituted
for that relative estimate. -/
theorem actualFullProjectedCLM_sub_squarefree_le_of_transferBounds
    [Nonempty Head]
    (xi : B.ParamSpace)
    {Cpow epsilon rpow : ℝ}
    (hCpow : 0 ≤ Cpow) (hepsilon : 0 ≤ epsilon) (hrpow : 0 ≤ rpow)
    (hW : 1 < B.sampleData.W)
    (h75 : PaperPrimePowerLemma75.PrimePowerTransferBounds
      (B.actualValuationLaw xi) B.sampleData.n B.sampleData.W Cpow epsilon)
    (hbudget : ∀ i : Band,
      3 * Cpow *
          (PrimeSums.bandTReciprocalSum
            B.sampleData.n B.sampleData.W + 1) *
            (1 / (B.sampleData.W : ℝ)) +
        3 * epsilon *
          (PrimeSums.bandTReciprocalSum
              B.sampleData.n B.sampleData.W / B.partition.center i + 1) *
            (1 / (B.sampleData.W : ℝ)) ≤ rpow)
    (q : PaperWeightedInverseExport.SharpGaugeSpace
      B.partition.mass B.partition.center) :
    ‖(B.actualFullProjectedCLM xi -
        B.actualSquarefreeProjectedCLM xi) q‖ ≤
      (2 * rpow) * ‖q‖ := by
  let omega := MovingLowGaugeTransfer.sharpWeight
    B.partition.mass B.partition.center
  let fullRow : (Band → ℝ) → Band → ℝ := fun b i ↦
    PrimePowerSharpBandTransfer.fullSharpRow
      (B.actualValuationLaw xi) B.partition b i
  let squarefreeRow : (Band → ℝ) → Band → ℝ := fun b i ↦
    SquarefreeSharpBandTransfer.squarefreeSharpRow
      (B.actualValuationLaw xi) B.partition b i
  have hraw (i : Band) :
      |fullRow q.1 i - squarefreeRow q.1 i| ≤ rpow * ‖q‖ := by
    by_cases hqzero : ‖q‖ = 0
    · have hq0 : q = 0 := norm_eq_zero.mp hqzero
      subst q
      have hfull : fullRow (0 : Band → ℝ) i = 0 := by
        simpa only [fullRow, zero_smul, zero_mul] using
          B.fullSharpRow_smul xi 0 (0 : Band → ℝ) i
      have hsf : squarefreeRow (0 : Band → ℝ) i = 0 := by
        simpa only [squarefreeRow, zero_smul, zero_mul] using
          B.squarefreeSharpRow_smul xi 0 (0 : Band → ℝ) i
      have hcoe :
          (((0 : PaperWeightedInverseExport.SharpGaugeSpace
            B.partition.mass B.partition.center) :
              PaperWeightedInverseExport.SharpGaugeSpace
                B.partition.mass B.partition.center) : Band → ℝ) = 0 := rfl
      rw [hcoe]
      rw [hfull, hsf, sub_self, abs_zero, norm_zero, mul_zero]
    · have hqpos : 0 < ‖q‖ := lt_of_le_of_ne (norm_nonneg q) (Ne.symm hqzero)
      let q0 : Band → ℝ := fun j ↦ q.1 j / ‖q‖
      have hq0unit (j : Band) : |q0 j| ≤ 1 := by
        have hj : |q.1 j| ≤ ‖q‖ := by
          rw [← Real.norm_eq_abs]
          exact norm_le_pi_norm q.1 j
        dsimp only [q0]
        rw [abs_div, abs_of_pos hqpos]
        exact (div_le_one hqpos).2 hj
      have hunit :=
        PrimePowerSharpBandTransfer.abs_fullSharpRow_sub_squarefreeSharpRow_le
          (B.actualValuationLaw xi) B.partition B.n_gt_one hW
          hCpow hepsilon h75 q0 hq0unit i
      have hunit' : |fullRow q0 i - squarefreeRow q0 i| ≤ rpow :=
        hunit.trans (hbudget i)
      have hqEq : q.1 = ‖q‖ • q0 := by
        funext j
        dsimp only [q0]
        simp only [Pi.smul_apply, smul_eq_mul]
        field_simp [hqzero]
      have hfull : fullRow q.1 i = ‖q‖ * fullRow q0 i := by
        rw [hqEq]
        exact B.fullSharpRow_smul xi ‖q‖ q0 i
      have hsf : squarefreeRow q.1 i = ‖q‖ * squarefreeRow q0 i := by
        rw [hqEq]
        exact B.squarefreeSharpRow_smul xi ‖q‖ q0 i
      rw [hfull, hsf, ← mul_sub, abs_mul, abs_of_pos hqpos]
      exact (mul_le_mul_of_nonneg_left hunit' hqpos.le).trans_eq
        (mul_comm ‖q‖ rpow)
  have hprojected (i : Band) :
      |FiniteGraphQuotientInverse.meanProjection omega
          (fullRow q.1) i -
        FiniteGraphQuotientInverse.meanProjection omega
          (squarefreeRow q.1) i| ≤ 2 * (rpow * ‖q‖) :=
    CompressedArithmeticOperator.abs_meanProjection_sub_le omega
      (fullRow q.1) (squarefreeRow q.1) (rpow * ‖q‖)
      (fun i ↦ MovingLowGaugeTransfer.sharpWeight_nonneg_of_mass_nonneg
        B.partition.mass B.partition.center
          (fun j ↦ (B.partition.data.mass_pos j).le) i)
      (actualSharpWeightTotal_pos B) hraw i
  have hnonneg : 0 ≤ (2 * rpow) * ‖q‖ := by positivity
  change ‖(((B.actualFullProjectedCLM xi -
      B.actualSquarefreeProjectedCLM xi) q :
        PaperWeightedInverseExport.SharpGaugeSpace
          B.partition.mass B.partition.center) : Band → ℝ)‖ ≤
    (2 * rpow) * ‖q‖
  rw [pi_norm_le_iff_of_nonneg hnonneg]
  intro i
  rw [Real.norm_eq_abs]
  exact hprojected i |>.trans_eq (by ring)

/-- Once the squarefree projected operator has been obtained from the
continuum/arithmetic reference, the literal Lemma 7.5 transfer yields an
inverse for the actual full-valuation operator.  The smallness condition is
exactly the displayed moving-low row budget, not an assumed invertibility. -/
theorem exists_actualFullProjectedEquiv_of_squarefree_of_transferBounds
    [Nonempty Head]
    (xi : B.ParamSpace)
    (squarefreeEquiv :
      PaperWeightedInverseExport.SharpGaugeSpace
          B.partition.mass B.partition.center ≃L[ℝ]
        PaperWeightedInverseExport.SharpGaugeSpace
          B.partition.mass B.partition.center)
    (hsquarefree : ∀ q, squarefreeEquiv q =
      B.actualSquarefreeProjectedCLM xi q)
    {C Cpow epsilon rpow : ℝ}
    (hC : 0 ≤ C) (hCpow : 0 ≤ Cpow)
    (hepsilon : 0 ≤ epsilon) (hrpow : 0 ≤ rpow)
    (hinv : ∀ v, ‖squarefreeEquiv.symm v‖ ≤ C * ‖v‖)
    (hsmall : C * (2 * rpow) < 1)
    (hW : 1 < B.sampleData.W)
    (h75 : PaperPrimePowerLemma75.PrimePowerTransferBounds
      (B.actualValuationLaw xi) B.sampleData.n B.sampleData.W Cpow epsilon)
    (hbudget : ∀ i : Band,
      3 * Cpow *
          (PrimeSums.bandTReciprocalSum
            B.sampleData.n B.sampleData.W + 1) *
            (1 / (B.sampleData.W : ℝ)) +
        3 * epsilon *
          (PrimeSums.bandTReciprocalSum
              B.sampleData.n B.sampleData.W / B.partition.center i + 1) *
            (1 / (B.sampleData.W : ℝ)) ≤ rpow) :
    ∃ actualEquiv :
      PaperWeightedInverseExport.SharpGaugeSpace
          B.partition.mass B.partition.center ≃L[ℝ]
        PaperWeightedInverseExport.SharpGaugeSpace
          B.partition.mass B.partition.center,
      (∀ q, actualEquiv q = B.actualFullProjectedCLM xi q) ∧
      ∀ v, ‖actualEquiv.symm v‖ ≤
        (C / (1 - C * (2 * rpow))) * ‖v‖ := by
  let A := B.actualSquarefreeProjectedCLM xi
  let Ainv : PaperWeightedInverseExport.SharpGaugeSpace
      B.partition.mass B.partition.center →L[ℝ]
      PaperWeightedInverseExport.SharpGaugeSpace
        B.partition.mass B.partition.center := squarefreeEquiv.symm
  let E := B.actualFullProjectedCLM xi - A
  have hleft (q : PaperWeightedInverseExport.SharpGaugeSpace
      B.partition.mass B.partition.center) : Ainv (A q) = q := by
    dsimp only [Ainv, A]
    rw [← hsquarefree q]
    exact squarefreeEquiv.symm_apply_apply q
  have hinv' (v : PaperWeightedInverseExport.SharpGaugeSpace
      B.partition.mass B.partition.center) : ‖Ainv v‖ ≤ C * ‖v‖ := hinv v
  have herror (q : PaperWeightedInverseExport.SharpGaugeSpace
      B.partition.mass B.partition.center) :
      ‖E q‖ ≤ (2 * rpow) * ‖q‖ := by
    dsimp only [E, A]
    exact B.actualFullProjectedCLM_sub_squarefree_le_of_transferBounds
      xi hCpow hepsilon hrpow hW h75 hbudget q
  let actualEquiv := StableInverse.perturbedEquiv
    A Ainv E C (2 * rpow) hC hsmall hleft hinv' herror
  refine ⟨actualEquiv, ?_, ?_⟩
  · intro q
    rw [StableInverse.perturbedEquiv_apply]
    dsimp only [actualEquiv, E]
    simp only [add_sub_cancel]
  · intro v
    exact StableInverse.perturbed_inverse_bound
      A Ainv E C (2 * rpow) hC hsmall hleft hinv' herror v

/-! ### Reference-law row attachment

The literal global-tilt form of Lemma 7.5 is naturally obtained first for an
unguarded component mixture.  The actual bridge law is a guard-deleted
mixture with a residual physical tilt.  The next elementary estimate keeps
that identification issue outside the prime-power algebra: a weighted
prime-row comparison for the full and squarefree covariance matrices moves
the Lemma 7.5 estimate from an arbitrary reference law to the actual law.
The only moving-low loss is displayed explicitly as `rho / center i`.
-/

private def sharpCovarianceRow
    (cov : ℕ → ℕ → ℝ)
    (P : Partition B.sampleData.n B.sampleData.W Band)
    (q : Band → ℝ) (i : Band) : ℝ :=
  ((1 / P.mass i) *
      ∑ p ∈ P.data.fiber i,
        ∑ r : BandPrime B.sampleData.n B.sampleData.W,
          (P.center (P.band r) * q (P.band r)) * cov p.1 r.1) /
    P.center i

private theorem abs_sharpCovarianceRow_sub_le_of_weightedPrimeRows
    (cov₁ cov₂ : ℕ → ℕ → ℝ)
    (P : Partition B.sampleData.n B.sampleData.W Band)
    {rho : ℝ}
    (hrow : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      (p.1 : ℝ) *
          ∑ r : BandPrime B.sampleData.n B.sampleData.W,
            |cov₁ p.1 r.1 - cov₂ p.1 r.1| ≤ rho)
    (q : Band → ℝ) (hq : ∀ j, |q j| ≤ 1) (i : Band) :
    |sharpCovarianceRow B cov₁ P q i -
        sharpCovarianceRow B cov₂ P q i| ≤ rho / P.center i := by
  have hmass : 0 < P.mass i := P.data.mass_pos i
  have hcenter : 0 < P.center i := P.center_pos B.n_gt_one i
  have hcenterNonneg (j : Band) : 0 ≤ P.center j :=
    (P.center_pos B.n_gt_one j).le
  have hcenterOne (j : Band) : P.center j ≤ 1 :=
    (P.center_mem_zero_one B.n_gt_one j).2
  have hcoeff (j : Band) : |P.center j * q j| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg (hcenterNonneg j)]
    exact (mul_le_mul_of_nonneg_left (hq j) (hcenterNonneg j)).trans
      (by simpa only [mul_one] using hcenterOne j)
  have hinner (p : BandPrime B.sampleData.n B.sampleData.W) :
      |(∑ r : BandPrime B.sampleData.n B.sampleData.W,
          (P.center (P.band r) * q (P.band r)) * cov₁ p.1 r.1) -
        (∑ r : BandPrime B.sampleData.n B.sampleData.W,
          (P.center (P.band r) * q (P.band r)) * cov₂ p.1 r.1)| ≤
        rho / (p.1 : ℝ) := by
    have hp : (0 : ℝ) < p.1 := by
      exact_mod_cast (prime_of_mem_primeBand p.2).pos
    calc
      |(∑ r : BandPrime B.sampleData.n B.sampleData.W,
          (P.center (P.band r) * q (P.band r)) * cov₁ p.1 r.1) -
        (∑ r : BandPrime B.sampleData.n B.sampleData.W,
          (P.center (P.band r) * q (P.band r)) * cov₂ p.1 r.1)| =
          |∑ r : BandPrime B.sampleData.n B.sampleData.W,
            (P.center (P.band r) * q (P.band r)) *
              (cov₁ p.1 r.1 - cov₂ p.1 r.1)| := by
            apply congrArg abs
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro r hr
            ring
      _ ≤ ∑ r : BandPrime B.sampleData.n B.sampleData.W,
          |(P.center (P.band r) * q (P.band r)) *
            (cov₁ p.1 r.1 - cov₂ p.1 r.1)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ r : BandPrime B.sampleData.n B.sampleData.W,
          |cov₁ p.1 r.1 - cov₂ p.1 r.1| := by
        apply Finset.sum_le_sum
        intro r hr
        rw [abs_mul]
        simpa only [one_mul] using mul_le_mul_of_nonneg_right
          (hcoeff (P.band r)) (abs_nonneg _)
      _ ≤ rho / (p.1 : ℝ) := by
        apply (le_div_iff₀ hp).2
        have hpRow := hrow p
        nlinarith
  have hsum :
      |(∑ p ∈ P.data.fiber i,
          ∑ r : BandPrime B.sampleData.n B.sampleData.W,
            (P.center (P.band r) * q (P.band r)) * cov₁ p.1 r.1) -
        (∑ p ∈ P.data.fiber i,
          ∑ r : BandPrime B.sampleData.n B.sampleData.W,
            (P.center (P.band r) * q (P.band r)) * cov₂ p.1 r.1)| ≤
        rho * P.mass i := by
    calc
      |(∑ p ∈ P.data.fiber i,
          ∑ r : BandPrime B.sampleData.n B.sampleData.W,
            (P.center (P.band r) * q (P.band r)) * cov₁ p.1 r.1) -
        (∑ p ∈ P.data.fiber i,
          ∑ r : BandPrime B.sampleData.n B.sampleData.W,
            (P.center (P.band r) * q (P.band r)) * cov₂ p.1 r.1)| =
          |∑ p ∈ P.data.fiber i,
            ((∑ r : BandPrime B.sampleData.n B.sampleData.W,
                (P.center (P.band r) * q (P.band r)) * cov₁ p.1 r.1) -
              ∑ r : BandPrime B.sampleData.n B.sampleData.W,
                (P.center (P.band r) * q (P.band r)) * cov₂ p.1 r.1)| := by
            congr 1
            rw [Finset.sum_sub_distrib]
      _ ≤ ∑ p ∈ P.data.fiber i,
          |(∑ r : BandPrime B.sampleData.n B.sampleData.W,
              (P.center (P.band r) * q (P.band r)) * cov₁ p.1 r.1) -
            ∑ r : BandPrime B.sampleData.n B.sampleData.W,
              (P.center (P.band r) * q (P.band r)) * cov₂ p.1 r.1| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ p ∈ P.data.fiber i, rho / (p.1 : ℝ) := by
        apply Finset.sum_le_sum
        intro p hp
        exact hinner p
      _ = rho * P.mass i := by
        rw [show P.mass i =
          ∑ p ∈ P.data.fiber i, 1 / (p.1 : ℝ) by rfl]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        ring
  unfold sharpCovarianceRow
  rw [← sub_div, abs_div, abs_of_pos hcenter]
  apply div_le_div_of_nonneg_right _ hcenter.le
  rw [← mul_sub, abs_mul, abs_of_pos (one_div_pos.mpr hmass)]
  calc
    (1 / P.mass i) *
        |(∑ p ∈ P.data.fiber i,
            ∑ r : BandPrime B.sampleData.n B.sampleData.W,
              (P.center (P.band r) * q (P.band r)) * cov₁ p.1 r.1) -
          ∑ p ∈ P.data.fiber i,
            ∑ r : BandPrime B.sampleData.n B.sampleData.W,
              (P.center (P.band r) * q (P.band r)) * cov₂ p.1 r.1| ≤
        (1 / P.mass i) * (rho * P.mass i) :=
      mul_le_mul_of_nonneg_left hsum (one_div_nonneg.mpr hmass.le)
    _ = rho := by field_simp [ne_of_gt hmass]

/-- Move the full-versus-squarefree sharp estimate from an arbitrary
reference law to the actual bridge law.  This is the exact interface needed
for guard deletion and the residual physical tilt: they need only supply the
two weighted covariance-row discrepancies `rhoFull` and `rhoSquarefree`. -/
theorem abs_actual_fullSharpRow_sub_squarefreeSharpRow_le_of_referenceLaw
    [Nonempty Head]
    {OmegaRef : Type*} [Fintype OmegaRef] {MRef : ℕ}
    (xi : B.ParamSpace)
    (referenceLaw : BoundedValuationLaw OmegaRef MRef)
    {Cpow epsilon rhoFull rhoSquarefree : ℝ}
    (hCpow : 0 ≤ Cpow) (hepsilon : 0 ≤ epsilon)
    (hW : 1 < B.sampleData.W)
    (h75 : PaperPrimePowerLemma75.PrimePowerTransferBounds referenceLaw
      B.sampleData.n B.sampleData.W Cpow epsilon)
    (hfullRow : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      (p.1 : ℝ) *
          ∑ r : BandPrime B.sampleData.n B.sampleData.W,
            |(B.actualValuationLaw xi).covVV p.1 r.1 -
              referenceLaw.covVV p.1 r.1| ≤ rhoFull)
    (hsquarefreeRow : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      (p.1 : ℝ) *
          ∑ r : BandPrime B.sampleData.n B.sampleData.W,
            |(B.actualValuationLaw xi).covII p.1 r.1 -
              referenceLaw.covII p.1 r.1| ≤ rhoSquarefree)
    (q : Band → ℝ) (hq : ∀ j, |q j| ≤ 1) (i : Band) :
    |PrimePowerSharpBandTransfer.fullSharpRow
          (B.actualValuationLaw xi) B.partition q i -
        SquarefreeSharpBandTransfer.squarefreeSharpRow
          (B.actualValuationLaw xi) B.partition q i| ≤
      3 * Cpow *
          (PrimeSums.bandTReciprocalSum
            B.sampleData.n B.sampleData.W + 1) *
            (1 / (B.sampleData.W : ℝ)) +
        3 * epsilon *
          (PrimeSums.bandTReciprocalSum
              B.sampleData.n B.sampleData.W / B.partition.center i + 1) *
            (1 / (B.sampleData.W : ℝ)) +
        (rhoFull + rhoSquarefree) / B.partition.center i := by
  have hfull := abs_sharpCovarianceRow_sub_le_of_weightedPrimeRows B
    (B.actualValuationLaw xi).covVV referenceLaw.covVV B.partition
    hfullRow q hq i
  have hsf := abs_sharpCovarianceRow_sub_le_of_weightedPrimeRows B
    (B.actualValuationLaw xi).covII referenceLaw.covII B.partition
    hsquarefreeRow q hq i
  have href :=
    PrimePowerSharpBandTransfer.abs_fullSharpRow_sub_squarefreeSharpRow_le
      referenceLaw B.partition B.n_gt_one hW hCpow hepsilon h75 q hq i
  have hfullDef : sharpCovarianceRow B
      (B.actualValuationLaw xi).covVV B.partition q i =
      PrimePowerSharpBandTransfer.fullSharpRow
        (B.actualValuationLaw xi) B.partition q i := rfl
  have hrefFullDef : sharpCovarianceRow B referenceLaw.covVV
      B.partition q i =
      PrimePowerSharpBandTransfer.fullSharpRow
        referenceLaw B.partition q i := rfl
  have hsfDef : sharpCovarianceRow B
      (B.actualValuationLaw xi).covII B.partition q i =
      SquarefreeSharpBandTransfer.squarefreeSharpRow
        (B.actualValuationLaw xi) B.partition q i := rfl
  have hrefSfDef : sharpCovarianceRow B referenceLaw.covII
      B.partition q i =
      SquarefreeSharpBandTransfer.squarefreeSharpRow
        referenceLaw B.partition q i := rfl
  rw [hfullDef, hrefFullDef] at hfull
  rw [hsfDef, hrefSfDef] at hsf
  have htriangle :
      |PrimePowerSharpBandTransfer.fullSharpRow
          (B.actualValuationLaw xi) B.partition q i -
        SquarefreeSharpBandTransfer.squarefreeSharpRow
          (B.actualValuationLaw xi) B.partition q i| ≤
        |PrimePowerSharpBandTransfer.fullSharpRow
            (B.actualValuationLaw xi) B.partition q i -
          PrimePowerSharpBandTransfer.fullSharpRow
            referenceLaw B.partition q i| +
        |PrimePowerSharpBandTransfer.fullSharpRow
            referenceLaw B.partition q i -
          SquarefreeSharpBandTransfer.squarefreeSharpRow
            referenceLaw B.partition q i| +
        |SquarefreeSharpBandTransfer.squarefreeSharpRow
            referenceLaw B.partition q i -
          SquarefreeSharpBandTransfer.squarefreeSharpRow
            (B.actualValuationLaw xi) B.partition q i| := by
    let x := PrimePowerSharpBandTransfer.fullSharpRow
      (B.actualValuationLaw xi) B.partition q i -
        PrimePowerSharpBandTransfer.fullSharpRow
          referenceLaw B.partition q i
    let y := PrimePowerSharpBandTransfer.fullSharpRow
      referenceLaw B.partition q i -
        SquarefreeSharpBandTransfer.squarefreeSharpRow
          referenceLaw B.partition q i
    let z := SquarefreeSharpBandTransfer.squarefreeSharpRow
      referenceLaw B.partition q i -
        SquarefreeSharpBandTransfer.squarefreeSharpRow
          (B.actualValuationLaw xi) B.partition q i
    have hdecomp :
        PrimePowerSharpBandTransfer.fullSharpRow
            (B.actualValuationLaw xi) B.partition q i -
          SquarefreeSharpBandTransfer.squarefreeSharpRow
            (B.actualValuationLaw xi) B.partition q i = x + y + z := by
      dsimp only [x, y, z]
      ring
    rw [hdecomp]
    change |x + y + z| ≤ |x| + |y| + |z|
    calc
      |x + y + z| ≤ |x + y| + |z| := abs_add_le _ _
      _ ≤ |x| + |y| + |z| := by
        linarith [abs_add_le x y]
  have hsf' :
      |SquarefreeSharpBandTransfer.squarefreeSharpRow
          referenceLaw B.partition q i -
        SquarefreeSharpBandTransfer.squarefreeSharpRow
          (B.actualValuationLaw xi) B.partition q i| ≤
        rhoSquarefree / B.partition.center i := by
    rw [abs_sub_comm]
    exact hsf
  calc
    |_ - _| ≤ _ := htriangle
    _ ≤ rhoFull / B.partition.center i +
          (3 * Cpow *
            (PrimeSums.bandTReciprocalSum
              B.sampleData.n B.sampleData.W + 1) *
              (1 / (B.sampleData.W : ℝ)) +
            3 * epsilon *
              (PrimeSums.bandTReciprocalSum
                  B.sampleData.n B.sampleData.W /
                    B.partition.center i + 1) *
                (1 / (B.sampleData.W : ℝ))) +
          rhoSquarefree / B.partition.center i := by
      gcongr
    _ = _ := by
      have hc : B.partition.center i ≠ 0 :=
        ne_of_gt (B.partition.center_pos B.n_gt_one i)
      field_simp [hc]
      ring

private theorem sharpCovarianceRow_sub
    (cov₁ cov₂ : ℕ → ℕ → ℝ)
    (P : Partition B.sampleData.n B.sampleData.W Band)
    (q : Band → ℝ) (i : Band) :
    sharpCovarianceRow B (fun p r ↦ cov₁ p r - cov₂ p r) P q i =
      sharpCovarianceRow B cov₁ P q i -
        sharpCovarianceRow B cov₂ P q i := by
  unfold sharpCovarianceRow
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  ring

/-- The sharper reference attachment needed by the global guard theorem:
only the `VV-II` power-correction row is compared between the actual and
reference laws.  This avoids charging two unrelated covariance errors and
matches `PaperGuardPowerCorrectionMixture` literally. -/
theorem abs_actual_fullSharpRow_sub_squarefreeSharpRow_le_of_referencePowerCorrectionRow
    [Nonempty Head]
    {OmegaRef : Type*} [Fintype OmegaRef] {MRef : ℕ}
    (xi : B.ParamSpace)
    (referenceLaw : BoundedValuationLaw OmegaRef MRef)
    {Cpow epsilon rhoPower : ℝ}
    (hCpow : 0 ≤ Cpow) (hepsilon : 0 ≤ epsilon)
    (hW : 1 < B.sampleData.W)
    (h75 : PaperPrimePowerLemma75.PrimePowerTransferBounds referenceLaw
      B.sampleData.n B.sampleData.W Cpow epsilon)
    (hpowerRow : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      (p.1 : ℝ) *
          ∑ r : BandPrime B.sampleData.n B.sampleData.W,
            |((B.actualValuationLaw xi).covVV p.1 r.1 -
                (B.actualValuationLaw xi).covII p.1 r.1) -
              (referenceLaw.covVV p.1 r.1 -
                referenceLaw.covII p.1 r.1)| ≤ rhoPower)
    (q : Band → ℝ) (hq : ∀ j, |q j| ≤ 1) (i : Band) :
    |PrimePowerSharpBandTransfer.fullSharpRow
          (B.actualValuationLaw xi) B.partition q i -
        SquarefreeSharpBandTransfer.squarefreeSharpRow
          (B.actualValuationLaw xi) B.partition q i| ≤
      3 * Cpow *
          (PrimeSums.bandTReciprocalSum
            B.sampleData.n B.sampleData.W + 1) *
            (1 / (B.sampleData.W : ℝ)) +
        3 * epsilon *
          (PrimeSums.bandTReciprocalSum
              B.sampleData.n B.sampleData.W / B.partition.center i + 1) *
            (1 / (B.sampleData.W : ℝ)) +
        rhoPower / B.partition.center i := by
  let actualCorrection : ℕ → ℕ → ℝ := fun p r ↦
    (B.actualValuationLaw xi).covVV p r -
      (B.actualValuationLaw xi).covII p r
  let referenceCorrection : ℕ → ℕ → ℝ := fun p r ↦
    referenceLaw.covVV p r - referenceLaw.covII p r
  have hpert := abs_sharpCovarianceRow_sub_le_of_weightedPrimeRows B
    actualCorrection referenceCorrection B.partition hpowerRow q hq i
  have hactual : sharpCovarianceRow B actualCorrection B.partition q i =
      PrimePowerSharpBandTransfer.fullSharpRow
          (B.actualValuationLaw xi) B.partition q i -
        SquarefreeSharpBandTransfer.squarefreeSharpRow
          (B.actualValuationLaw xi) B.partition q i := by
    dsimp only [actualCorrection]
    rw [B.sharpCovarianceRow_sub]
    rfl
  have hrefCorrection :
      sharpCovarianceRow B referenceCorrection B.partition q i =
        PrimePowerSharpBandTransfer.fullSharpRow
            referenceLaw B.partition q i -
          SquarefreeSharpBandTransfer.squarefreeSharpRow
            referenceLaw B.partition q i := by
    dsimp only [referenceCorrection]
    rw [B.sharpCovarianceRow_sub]
    rfl
  rw [hactual, hrefCorrection] at hpert
  have href :=
    PrimePowerSharpBandTransfer.abs_fullSharpRow_sub_squarefreeSharpRow_le
      referenceLaw B.partition B.n_gt_one hW hCpow hepsilon h75 q hq i
  let actualDelta :=
    PrimePowerSharpBandTransfer.fullSharpRow
        (B.actualValuationLaw xi) B.partition q i -
      SquarefreeSharpBandTransfer.squarefreeSharpRow
        (B.actualValuationLaw xi) B.partition q i
  let referenceDelta :=
    PrimePowerSharpBandTransfer.fullSharpRow referenceLaw B.partition q i -
      SquarefreeSharpBandTransfer.squarefreeSharpRow
        referenceLaw B.partition q i
  have htriangle : |actualDelta| ≤
      |actualDelta - referenceDelta| + |referenceDelta| := by
    have h := abs_add_le (actualDelta - referenceDelta) referenceDelta
    simpa only [sub_add_cancel] using h
  calc
    |_ - _| = |actualDelta| := rfl
    _ ≤ |actualDelta - referenceDelta| + |referenceDelta| := htriangle
    _ ≤ rhoPower / B.partition.center i +
        (3 * Cpow *
          (PrimeSums.bandTReciprocalSum
            B.sampleData.n B.sampleData.W + 1) *
              (1 / (B.sampleData.W : ℝ)) +
          3 * epsilon *
            (PrimeSums.bandTReciprocalSum
                B.sampleData.n B.sampleData.W /
                  B.partition.center i + 1) *
              (1 / (B.sampleData.W : ℝ))) :=
      add_le_add hpert href
    _ = _ := by ring

/-- A literal unit sharp-row estimate yields the projected operator-norm
estimate with the exact factor two from weighted-mean projection.  This
public form lets the fully assembled canonical Lemma 7.5 row be consumed
without re-exposing its internal reference law or transfer certificate. -/
theorem actualFullProjectedCLM_sub_squarefree_le_of_unitSharpRows
    [Nonempty Head]
    (xi : B.ParamSpace) {rpow : ℝ} (hrpow : 0 ≤ rpow)
    (hunit : ∀ q : Band → ℝ, (∀ j, |q j| ≤ 1) → ∀ i : Band,
      |PrimePowerSharpBandTransfer.fullSharpRow
          (B.actualValuationLaw xi) B.partition q i -
        SquarefreeSharpBandTransfer.squarefreeSharpRow
          (B.actualValuationLaw xi) B.partition q i| ≤ rpow)
    (q : PaperWeightedInverseExport.SharpGaugeSpace
      B.partition.mass B.partition.center) :
    ‖(B.actualFullProjectedCLM xi -
        B.actualSquarefreeProjectedCLM xi) q‖ ≤
      (2 * rpow) * ‖q‖ := by
  let omega := MovingLowGaugeTransfer.sharpWeight
    B.partition.mass B.partition.center
  let fullRow : (Band → ℝ) → Band → ℝ := fun b i ↦
    PrimePowerSharpBandTransfer.fullSharpRow
      (B.actualValuationLaw xi) B.partition b i
  let squarefreeRow : (Band → ℝ) → Band → ℝ := fun b i ↦
    SquarefreeSharpBandTransfer.squarefreeSharpRow
      (B.actualValuationLaw xi) B.partition b i
  have hraw (i : Band) :
      |fullRow q.1 i - squarefreeRow q.1 i| ≤ rpow * ‖q‖ := by
    by_cases hqzero : ‖q‖ = 0
    · have hq0 : q = 0 := norm_eq_zero.mp hqzero
      subst q
      have hfull : fullRow (0 : Band → ℝ) i = 0 := by
        simpa only [fullRow, zero_smul, zero_mul] using
          B.fullSharpRow_smul xi 0 (0 : Band → ℝ) i
      have hsf : squarefreeRow (0 : Band → ℝ) i = 0 := by
        simpa only [squarefreeRow, zero_smul, zero_mul] using
          B.squarefreeSharpRow_smul xi 0 (0 : Band → ℝ) i
      have hcoe :
          (((0 : PaperWeightedInverseExport.SharpGaugeSpace
            B.partition.mass B.partition.center) :
              PaperWeightedInverseExport.SharpGaugeSpace
                B.partition.mass B.partition.center) : Band → ℝ) = 0 := rfl
      rw [hcoe]
      rw [hfull, hsf, sub_self, abs_zero, norm_zero, mul_zero]
    · have hqpos : 0 < ‖q‖ :=
        lt_of_le_of_ne (norm_nonneg q) (Ne.symm hqzero)
      let q0 : Band → ℝ := fun j ↦ q.1 j / ‖q‖
      have hq0unit (j : Band) : |q0 j| ≤ 1 := by
        have hj : |q.1 j| ≤ ‖q‖ := by
          rw [← Real.norm_eq_abs]
          exact norm_le_pi_norm q.1 j
        dsimp only [q0]
        rw [abs_div, abs_of_pos hqpos]
        exact (div_le_one hqpos).2 hj
      have hunit' : |fullRow q0 i - squarefreeRow q0 i| ≤ rpow := by
        exact hunit q0 hq0unit i
      have hqEq : q.1 = ‖q‖ • q0 := by
        funext j
        dsimp only [q0]
        simp only [Pi.smul_apply, smul_eq_mul]
        field_simp [hqzero]
      have hfull : fullRow q.1 i = ‖q‖ * fullRow q0 i := by
        rw [hqEq]
        exact B.fullSharpRow_smul xi ‖q‖ q0 i
      have hsf : squarefreeRow q.1 i = ‖q‖ * squarefreeRow q0 i := by
        rw [hqEq]
        exact B.squarefreeSharpRow_smul xi ‖q‖ q0 i
      rw [hfull, hsf, ← mul_sub, abs_mul, abs_of_pos hqpos]
      exact (mul_le_mul_of_nonneg_left hunit' hqpos.le).trans_eq
        (mul_comm ‖q‖ rpow)
  have hprojected (i : Band) :
      |FiniteGraphQuotientInverse.meanProjection omega
          (fullRow q.1) i -
        FiniteGraphQuotientInverse.meanProjection omega
          (squarefreeRow q.1) i| ≤ 2 * (rpow * ‖q‖) :=
    CompressedArithmeticOperator.abs_meanProjection_sub_le omega
      (fullRow q.1) (squarefreeRow q.1) (rpow * ‖q‖)
      (fun i ↦ MovingLowGaugeTransfer.sharpWeight_nonneg_of_mass_nonneg
        B.partition.mass B.partition.center
          (fun j ↦ (B.partition.data.mass_pos j).le) i)
      (actualSharpWeightTotal_pos B) hraw i
  have hnonneg : 0 ≤ (2 * rpow) * ‖q‖ := by positivity
  change ‖(((B.actualFullProjectedCLM xi -
      B.actualSquarefreeProjectedCLM xi) q :
        PaperWeightedInverseExport.SharpGaugeSpace
          B.partition.mass B.partition.center) : Band → ℝ)‖ ≤
    (2 * rpow) * ‖q‖
  rw [pi_norm_le_iff_of_nonneg hnonneg]
  intro i
  rw [Real.norm_eq_abs]
  exact hprojected i |>.trans_eq (by ring)

/-- Projected actual full-valuation transfer from a Lemma 7.5 reference law.
The concrete guard/physical comparison enters only through the two weighted
prime-row errors, and its moving-low cost remains visible in `hbudget`. -/
theorem actualFullProjectedCLM_sub_squarefree_le_of_referenceLaw
    [Nonempty Head]
    {OmegaRef : Type*} [Fintype OmegaRef] {MRef : ℕ}
    (xi : B.ParamSpace)
    (referenceLaw : BoundedValuationLaw OmegaRef MRef)
    {Cpow epsilon rhoFull rhoSquarefree rpow : ℝ}
    (hCpow : 0 ≤ Cpow) (hepsilon : 0 ≤ epsilon)
    (hrpow : 0 ≤ rpow) (hW : 1 < B.sampleData.W)
    (h75 : PaperPrimePowerLemma75.PrimePowerTransferBounds referenceLaw
      B.sampleData.n B.sampleData.W Cpow epsilon)
    (hfullRow : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      (p.1 : ℝ) *
          ∑ r : BandPrime B.sampleData.n B.sampleData.W,
            |(B.actualValuationLaw xi).covVV p.1 r.1 -
              referenceLaw.covVV p.1 r.1| ≤ rhoFull)
    (hsquarefreeRow : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      (p.1 : ℝ) *
          ∑ r : BandPrime B.sampleData.n B.sampleData.W,
            |(B.actualValuationLaw xi).covII p.1 r.1 -
              referenceLaw.covII p.1 r.1| ≤ rhoSquarefree)
    (hbudget : ∀ i : Band,
      3 * Cpow *
          (PrimeSums.bandTReciprocalSum
            B.sampleData.n B.sampleData.W + 1) *
            (1 / (B.sampleData.W : ℝ)) +
        3 * epsilon *
          (PrimeSums.bandTReciprocalSum
              B.sampleData.n B.sampleData.W / B.partition.center i + 1) *
            (1 / (B.sampleData.W : ℝ)) +
        (rhoFull + rhoSquarefree) / B.partition.center i ≤ rpow)
    (q : PaperWeightedInverseExport.SharpGaugeSpace
      B.partition.mass B.partition.center) :
    ‖(B.actualFullProjectedCLM xi -
        B.actualSquarefreeProjectedCLM xi) q‖ ≤
      (2 * rpow) * ‖q‖ := by
  apply B.actualFullProjectedCLM_sub_squarefree_le_of_unitSharpRows
    xi hrpow _ q
  intro b hb i
  exact (B.abs_actual_fullSharpRow_sub_squarefreeSharpRow_le_of_referenceLaw
    xi referenceLaw hCpow hepsilon hW h75 hfullRow hsquarefreeRow b hb i).trans
      (hbudget i)

/-- Projected version of the direct `VV-II` reference attachment. -/
theorem actualFullProjectedCLM_sub_squarefree_le_of_referencePowerCorrectionRow
    [Nonempty Head]
    {OmegaRef : Type*} [Fintype OmegaRef] {MRef : ℕ}
    (xi : B.ParamSpace)
    (referenceLaw : BoundedValuationLaw OmegaRef MRef)
    {Cpow epsilon rhoPower rpow : ℝ}
    (hCpow : 0 ≤ Cpow) (hepsilon : 0 ≤ epsilon)
    (hrpow : 0 ≤ rpow) (hW : 1 < B.sampleData.W)
    (h75 : PaperPrimePowerLemma75.PrimePowerTransferBounds referenceLaw
      B.sampleData.n B.sampleData.W Cpow epsilon)
    (hpowerRow : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      (p.1 : ℝ) *
          ∑ r : BandPrime B.sampleData.n B.sampleData.W,
            |((B.actualValuationLaw xi).covVV p.1 r.1 -
                (B.actualValuationLaw xi).covII p.1 r.1) -
              (referenceLaw.covVV p.1 r.1 -
                referenceLaw.covII p.1 r.1)| ≤ rhoPower)
    (hbudget : ∀ i : Band,
      3 * Cpow *
          (PrimeSums.bandTReciprocalSum
            B.sampleData.n B.sampleData.W + 1) *
            (1 / (B.sampleData.W : ℝ)) +
        3 * epsilon *
          (PrimeSums.bandTReciprocalSum
              B.sampleData.n B.sampleData.W / B.partition.center i + 1) *
            (1 / (B.sampleData.W : ℝ)) +
        rhoPower / B.partition.center i ≤ rpow)
    (q : PaperWeightedInverseExport.SharpGaugeSpace
      B.partition.mass B.partition.center) :
    ‖(B.actualFullProjectedCLM xi -
        B.actualSquarefreeProjectedCLM xi) q‖ ≤
      (2 * rpow) * ‖q‖ := by
  apply B.actualFullProjectedCLM_sub_squarefree_le_of_unitSharpRows
    xi hrpow _ q
  intro b hb i
  exact
    (B.abs_actual_fullSharpRow_sub_squarefreeSharpRow_le_of_referencePowerCorrectionRow
      xi referenceLaw hCpow hepsilon hW h75 hpowerRow b hb i).trans
        (hbudget i)

/-- Stable inverse for the actual full-valuation projected operator, starting
from a reference-law Lemma 7.5 certificate rather than assuming the
certificate directly on the guard-deleted actual law. -/
theorem exists_actualFullProjectedEquiv_of_squarefree_of_referenceLaw
    [Nonempty Head]
    {OmegaRef : Type*} [Fintype OmegaRef] {MRef : ℕ}
    (xi : B.ParamSpace)
    (referenceLaw : BoundedValuationLaw OmegaRef MRef)
    (squarefreeEquiv :
      PaperWeightedInverseExport.SharpGaugeSpace
          B.partition.mass B.partition.center ≃L[ℝ]
        PaperWeightedInverseExport.SharpGaugeSpace
          B.partition.mass B.partition.center)
    (hsquarefree : ∀ q, squarefreeEquiv q =
      B.actualSquarefreeProjectedCLM xi q)
    {C Cpow epsilon rhoFull rhoSquarefree rpow : ℝ}
    (hC : 0 ≤ C) (hCpow : 0 ≤ Cpow) (hepsilon : 0 ≤ epsilon)
    (hrpow : 0 ≤ rpow)
    (hinv : ∀ v, ‖squarefreeEquiv.symm v‖ ≤ C * ‖v‖)
    (hsmall : C * (2 * rpow) < 1)
    (hW : 1 < B.sampleData.W)
    (h75 : PaperPrimePowerLemma75.PrimePowerTransferBounds referenceLaw
      B.sampleData.n B.sampleData.W Cpow epsilon)
    (hfullRow : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      (p.1 : ℝ) *
          ∑ r : BandPrime B.sampleData.n B.sampleData.W,
            |(B.actualValuationLaw xi).covVV p.1 r.1 -
              referenceLaw.covVV p.1 r.1| ≤ rhoFull)
    (hsquarefreeRow : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      (p.1 : ℝ) *
          ∑ r : BandPrime B.sampleData.n B.sampleData.W,
            |(B.actualValuationLaw xi).covII p.1 r.1 -
              referenceLaw.covII p.1 r.1| ≤ rhoSquarefree)
    (hbudget : ∀ i : Band,
      3 * Cpow *
          (PrimeSums.bandTReciprocalSum
            B.sampleData.n B.sampleData.W + 1) *
            (1 / (B.sampleData.W : ℝ)) +
        3 * epsilon *
          (PrimeSums.bandTReciprocalSum
              B.sampleData.n B.sampleData.W / B.partition.center i + 1) *
            (1 / (B.sampleData.W : ℝ)) +
        (rhoFull + rhoSquarefree) / B.partition.center i ≤ rpow) :
    ∃ actualEquiv :
      PaperWeightedInverseExport.SharpGaugeSpace
          B.partition.mass B.partition.center ≃L[ℝ]
        PaperWeightedInverseExport.SharpGaugeSpace
          B.partition.mass B.partition.center,
      (∀ q, actualEquiv q = B.actualFullProjectedCLM xi q) ∧
      ∀ v, ‖actualEquiv.symm v‖ ≤
        (C / (1 - C * (2 * rpow))) * ‖v‖ := by
  let A := B.actualSquarefreeProjectedCLM xi
  let Ainv : PaperWeightedInverseExport.SharpGaugeSpace
      B.partition.mass B.partition.center →L[ℝ]
      PaperWeightedInverseExport.SharpGaugeSpace
        B.partition.mass B.partition.center := squarefreeEquiv.symm
  let E := B.actualFullProjectedCLM xi - A
  have hleft (q : PaperWeightedInverseExport.SharpGaugeSpace
      B.partition.mass B.partition.center) : Ainv (A q) = q := by
    dsimp only [Ainv, A]
    rw [← hsquarefree q]
    exact squarefreeEquiv.symm_apply_apply q
  have hinv' (v : PaperWeightedInverseExport.SharpGaugeSpace
      B.partition.mass B.partition.center) : ‖Ainv v‖ ≤ C * ‖v‖ := hinv v
  have herror (q : PaperWeightedInverseExport.SharpGaugeSpace
      B.partition.mass B.partition.center) :
      ‖E q‖ ≤ (2 * rpow) * ‖q‖ := by
    dsimp only [E, A]
    exact B.actualFullProjectedCLM_sub_squarefree_le_of_referenceLaw
      xi referenceLaw hCpow hepsilon hrpow hW h75 hfullRow
      hsquarefreeRow hbudget q
  let actualEquiv := StableInverse.perturbedEquiv
    A Ainv E C (2 * rpow) hC hsmall hleft hinv' herror
  refine ⟨actualEquiv, ?_, ?_⟩
  · intro q
    rw [StableInverse.perturbedEquiv_apply]
    dsimp only [actualEquiv, E]
    simp only [add_sub_cancel]
  · intro v
    exact StableInverse.perturbed_inverse_bound
      A Ainv E C (2 * rpow) hC hsmall hleft hinv' herror v

/-- Stable inverse obtained from the direct global `VV-II` reference-row
comparison supplied by guard deletion and residual-tilt stability. -/
theorem exists_actualFullProjectedEquiv_of_squarefree_of_referencePowerCorrectionRow
    [Nonempty Head]
    {OmegaRef : Type*} [Fintype OmegaRef] {MRef : ℕ}
    (xi : B.ParamSpace)
    (referenceLaw : BoundedValuationLaw OmegaRef MRef)
    (squarefreeEquiv :
      PaperWeightedInverseExport.SharpGaugeSpace
          B.partition.mass B.partition.center ≃L[ℝ]
        PaperWeightedInverseExport.SharpGaugeSpace
          B.partition.mass B.partition.center)
    (hsquarefree : ∀ q, squarefreeEquiv q =
      B.actualSquarefreeProjectedCLM xi q)
    {C Cpow epsilon rhoPower rpow : ℝ}
    (hC : 0 ≤ C) (hCpow : 0 ≤ Cpow) (hepsilon : 0 ≤ epsilon)
    (hrpow : 0 ≤ rpow)
    (hinv : ∀ v, ‖squarefreeEquiv.symm v‖ ≤ C * ‖v‖)
    (hsmall : C * (2 * rpow) < 1)
    (hW : 1 < B.sampleData.W)
    (h75 : PaperPrimePowerLemma75.PrimePowerTransferBounds referenceLaw
      B.sampleData.n B.sampleData.W Cpow epsilon)
    (hpowerRow : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      (p.1 : ℝ) *
          ∑ r : BandPrime B.sampleData.n B.sampleData.W,
            |((B.actualValuationLaw xi).covVV p.1 r.1 -
                (B.actualValuationLaw xi).covII p.1 r.1) -
              (referenceLaw.covVV p.1 r.1 -
                referenceLaw.covII p.1 r.1)| ≤ rhoPower)
    (hbudget : ∀ i : Band,
      3 * Cpow *
          (PrimeSums.bandTReciprocalSum
            B.sampleData.n B.sampleData.W + 1) *
            (1 / (B.sampleData.W : ℝ)) +
        3 * epsilon *
          (PrimeSums.bandTReciprocalSum
              B.sampleData.n B.sampleData.W / B.partition.center i + 1) *
            (1 / (B.sampleData.W : ℝ)) +
        rhoPower / B.partition.center i ≤ rpow) :
    ∃ actualEquiv :
      PaperWeightedInverseExport.SharpGaugeSpace
          B.partition.mass B.partition.center ≃L[ℝ]
        PaperWeightedInverseExport.SharpGaugeSpace
          B.partition.mass B.partition.center,
      (∀ q, actualEquiv q = B.actualFullProjectedCLM xi q) ∧
      ∀ v, ‖actualEquiv.symm v‖ ≤
        (C / (1 - C * (2 * rpow))) * ‖v‖ := by
  let A := B.actualSquarefreeProjectedCLM xi
  let Ainv : PaperWeightedInverseExport.SharpGaugeSpace
      B.partition.mass B.partition.center →L[ℝ]
      PaperWeightedInverseExport.SharpGaugeSpace
        B.partition.mass B.partition.center := squarefreeEquiv.symm
  let E := B.actualFullProjectedCLM xi - A
  have hleft (q : PaperWeightedInverseExport.SharpGaugeSpace
      B.partition.mass B.partition.center) : Ainv (A q) = q := by
    dsimp only [Ainv, A]
    rw [← hsquarefree q]
    exact squarefreeEquiv.symm_apply_apply q
  have hinv' (v : PaperWeightedInverseExport.SharpGaugeSpace
      B.partition.mass B.partition.center) : ‖Ainv v‖ ≤ C * ‖v‖ := hinv v
  have herror (q : PaperWeightedInverseExport.SharpGaugeSpace
      B.partition.mass B.partition.center) :
      ‖E q‖ ≤ (2 * rpow) * ‖q‖ := by
    dsimp only [E, A]
    exact
      B.actualFullProjectedCLM_sub_squarefree_le_of_referencePowerCorrectionRow
        xi referenceLaw hCpow hepsilon hrpow hW h75 hpowerRow hbudget q
  let actualEquiv := StableInverse.perturbedEquiv
    A Ainv E C (2 * rpow) hC hsmall hleft hinv' herror
  refine ⟨actualEquiv, ?_, ?_⟩
  · intro q
    rw [StableInverse.perturbedEquiv_apply]
    dsimp only [actualEquiv, E]
    simp only [add_sub_cancel]
  · intro v
    exact StableInverse.perturbed_inverse_bound
      A Ainv E C (2 * rpow) hC hsmall hleft hinv' herror v

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
