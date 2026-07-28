import Erdos390.Full.PaperGuardPowerCorrectionMixture
import Erdos390.Full.FiniteProbabilityMixtureGuardReindexing
import Erdos390.Full.PaperBridgeMediumValuationMixture
import Erdos390.Full.PaperGuardedStructuredSample
import Erdos390.Full.FixedFiniteMixtureGlobalTiltLemma75
import Erdos390.Full.GuardSquarefreeErrorRate
import Erdos390.Full.PaperStatisticNorm

/-!
# The canonical guard contribution to the prime-power correction row

The prime-power reference law in Lemma 8.4 lives on the unguarded raw
structured cells, whereas the medium-only bridge law lives on the literal
guard-deleted cells.  This file compares the two tagged mixtures without
changing their (post-tilt) component weights.  The comparison includes all
between-component covariance terms.

No arbitrary `BridgeData` is declared canonical.  The finite comparison is
stated under the exact equality between its `sampleData` field and the
canonical constructor from `PaperGuardedStructuredSample`; all dependent
sample-space identifications are then obtained from
`canonicalSampleData_cellFinset`.
-/

open scoped BigOperators
open Filter Topology

set_option maxRecDepth 5000

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open PrimePowerCovariance PrimePowerCovariance.BoundedValuationLaw
open StructuredCellValuationLaw StructuredCells
open PaperGuardCensus GuardedUniformCell
open ValuationScoreDomination

namespace BridgeData

private theorem sigmaMixture_tilt_covariance_eq_of_finset_family_eq
    {Cell₀ : Type*} [Fintype Cell₀]
    (S T : Cell₀ → Finset ℕ) (hST : S = T)
    (hS : ∀ c, (S c).Nonempty) (hT : ∀ c, (T c).Nonempty)
    (scoreS : ∀ c, S c → ℝ) (scoreT : ∀ c, T c → ℝ)
    (hscore : ∀ c (x : S c) (y : T c),
      (x : ℕ) = (y : ℕ) → scoreS c x = scoreT c y)
    (weight : FiniteProbability Cell₀) (F H : ℕ → ℝ) :
    (sigmaMixture weight (fun c ↦
        (uniformOnFinset (S c) (hS c)).exponentialTilt (scoreS c))).covariance
        (fun x ↦ F (x.2 : ℕ)) (fun x ↦ H (x.2 : ℕ)) =
      (sigmaMixture weight (fun c ↦
        (uniformOnFinset (T c) (hT c)).exponentialTilt (scoreT c))).covariance
        (fun x ↦ F (x.2 : ℕ)) (fun x ↦ H (x.2 : ℕ)) := by
  subst T
  have hscoreEq : scoreS = scoreT := by
    funext c x
    exact hscore c x x rfl
  subst scoreT
  have hproof : hS = hT := Subsingleton.elim _ _
  subst hT
  rfl

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- The unguarded, medium-prime tilted component, widened to one fixed
physical endpoint. -/
def canonicalRawMediumComponentLaw
    (P : Head → HeadPattern.Pattern) (I : PhysicalIntervals)
    (Cmax : ℝ) (xi : B.ParamSpace)
    (hC_le : ∀ sigma, I.upper sigma ≤ Cmax)
    (hS : ∀ c : Cell Head, (rawCell P I B.sampleData.n c).Nonempty)
    (c : Cell Head) :
    BoundedValuationLaw (rawCell P I B.sampleData.n c)
      (physicalBound Cmax B.sampleData.n) :=
  widen
    (valuationTilt (P c.1)
      (physicalBound (I.lower c.2) B.sampleData.n)
      (physicalBound (I.upper c.2) B.sampleData.n)
      (yNat B.sampleData.n) (hS c)
      (primeBand B.sampleData.n B.sampleData.W)
      (B.effectiveNatCoefficient xi) B.L)
    (FixedFiniteMixtureFullUniform.physicalBound_mono
      (hC_le c.2) B.sampleData.n)

/-- The raw unguarded tagged reference law, with exactly the component
weights carried by the actual post-tilt bridge law. -/
def canonicalRawMediumReferenceLaw [Nonempty Head]
    (P : Head → HeadPattern.Pattern) (I : PhysicalIntervals)
    (Cmax : ℝ) (xi : B.ParamSpace)
    (hC_le : ∀ sigma, I.upper sigma ≤ Cmax)
    (hS : ∀ c : Cell Head, (rawCell P I B.sampleData.n c).Nonempty) :
    BoundedValuationLaw
      (Sigma fun c : Cell Head ↦ rawCell P I B.sampleData.n c)
      (physicalBound Cmax B.sampleData.n) :=
  sigmaMixture
    (tiltedSigmaWeight B.baselineCellProbability
      B.guardedCellProbability (B.scaledBridgeScore xi))
    (B.canonicalRawMediumComponentLaw P I Cmax xi hC_le hS)

/-- The medium-only guard-deleted mixture with the actual post-tilt cell
weights.  This definition is deliberately local to the guard comparison;
the residual-physical comparison uses the definitionally identical law. -/
def canonicalGuardedMediumReferenceLaw [Nonempty Head]
    (xi : B.ParamSpace) :
    BoundedValuationLaw B.sampleData.Sample B.sampleEndpoint :=
  sigmaMixture
    (tiltedSigmaWeight B.baselineCellProbability
      B.guardedCellProbability (B.scaledBridgeScore xi))
    (B.mediumComponentValuationLaw xi)

@[simp] theorem canonicalRawMediumReferenceLaw_probability [Nonempty Head]
    (P : Head → HeadPattern.Pattern) (I : PhysicalIntervals)
    (Cmax : ℝ) (xi : B.ParamSpace)
    (hC_le : ∀ sigma, I.upper sigma ≤ Cmax)
    (hS : ∀ c : Cell Head, (rawCell P I B.sampleData.n c).Nonempty) :
    (B.canonicalRawMediumReferenceLaw P I Cmax xi hC_le hS).probability =
      sigmaMixture
        (tiltedSigmaWeight B.baselineCellProbability
          B.guardedCellProbability (B.scaledBridgeScore xi))
        (fun c ↦
          (uniformOnFinset (rawCell P I B.sampleData.n c) (hS c)).exponentialTilt
            (fun m ↦ valuationScore
              (primeBand B.sampleData.n B.sampleData.W)
              (B.effectiveNatCoefficient xi) B.L (m : ℕ))) := rfl

@[simp] theorem canonicalRawMediumReferenceLaw_value [Nonempty Head]
    (P : Head → HeadPattern.Pattern) (I : PhysicalIntervals)
    (Cmax : ℝ) (xi : B.ParamSpace)
    (hC_le : ∀ sigma, I.upper sigma ≤ Cmax)
    (hS : ∀ c : Cell Head, (rawCell P I B.sampleData.n c).Nonempty)
    (m : Sigma fun c : Cell Head ↦ rawCell P I B.sampleData.n c) :
    (B.canonicalRawMediumReferenceLaw P I Cmax xi hC_le hS).value m =
      (m.2 : ℕ) := rfl

/-- Exact canonical guard comparison.  The equality `hcanonical` is the
only place where the abstract bridge data is identified with the canonical
constructor.  In particular, the actual partition-function-reweighted
component weights are retained on both sides. -/
theorem sum_abs_physicalMediumReference_powerCorrection_sub_canonicalRaw_le
    [Nonempty Head]
    (P : Head → HeadPattern.Pattern) (I : PhysicalIntervals)
    (Cmax : ℝ) {Cprom Cbank : ℕ}
    (G : Ledger B.sampleData.n Cprom Cbank)
    (hsep : physicalBound (I.upper .minus) B.sampleData.n <
      physicalBound (I.lower .plus) B.sampleData.n)
    (hremaining : ∀ c : Cell Head,
      (rawCell P I B.sampleData.n c \ G.guards).Nonempty)
    (hcanonical : B.sampleData =
      canonicalSampleData (W := B.sampleData.W) P I G hsep hremaining)
    (xi : B.ParamSpace)
    (hC_le : ∀ sigma, I.upper sigma ≤ Cmax)
    (hW : 1 < B.sampleData.W)
    {K d : ℝ} (hK : 0 ≤ K) (hd : 0 ≤ d)
    (hEnvelope : ∀ c : Cell Head,
      valuationEnvelope I B.sampleData.n B.sampleData.W c ≤ K)
    (hsmall : ∀ c : Cell Head,
      (((uniformOnFinset (rawCell P I B.sampleData.n c)
          ((hremaining c).mono (Finset.sdiff_subset))).exponentialTilt
        (fun m ↦ valuationScore
          (primeBand B.sampleData.n B.sampleData.W)
          (B.effectiveNatCoefficient xi) B.L (m : ℕ))).guardMass
        (guardSubtype (rawCell P I B.sampleData.n c) G.guards) < 1))
    (hperturb : ∀ c : Cell Head,
      (((uniformOnFinset (rawCell P I B.sampleData.n c)
          ((hremaining c).mono (Finset.sdiff_subset))).exponentialTilt
        (fun m ↦ valuationScore
          (primeBand B.sampleData.n B.sampleData.W)
          (B.effectiveNatCoefficient xi) B.L (m : ℕ))).guardPerturbation
        (guardSubtype (rawCell P I B.sampleData.n c) G.guards) ≤ d))
    (p : BandPrime B.sampleData.n B.sampleData.W) :
    ∑ q : BandPrime B.sampleData.n B.sampleData.W,
      |((B.canonicalGuardedMediumReferenceLaw xi).covVV p.1 q.1 -
          (B.canonicalGuardedMediumReferenceLaw xi).covII p.1 q.1) -
        ((B.canonicalRawMediumReferenceLaw P I Cmax xi hC_le
            (fun c ↦ (hremaining c).mono Finset.sdiff_subset)).covVV p.1 q.1 -
          (B.canonicalRawMediumReferenceLaw P I Cmax xi hC_le
            (fun c ↦ (hremaining c).mono Finset.sdiff_subset)).covII p.1 q.1)| ≤
      PaperGuardCensus.guardPowerCorrectionRowError K d := by
  let hS : ∀ c : Cell Head, (rawCell P I B.sampleData.n c).Nonempty :=
    fun c ↦ (hremaining c).mono Finset.sdiff_subset
  let score : ∀ c : Cell Head, rawCell P I B.sampleData.n c → ℝ :=
    fun _ m ↦ valuationScore
      (primeBand B.sampleData.n B.sampleData.W)
      (B.effectiveNatCoefficient xi) B.L (m : ℕ)
  let weight := tiltedSigmaWeight B.baselineCellProbability
    B.guardedCellProbability (B.scaledBridgeScore xi)
  have hguard := PaperGuardCensus.sum_abs_guardDeleted_powerCorrectionRow_sub_le
    P I hW G.guards hS score weight p
      hK hd hEnvelope (by simpa only [hS, score] using hsmall)
      (by simpa only [hS, score] using hperturb)
  let S := fun c : Cell Head ↦ rawCell P I B.sampleData.n c
  let guards := fun _c : Cell Head ↦ G.guards
  let mu : ∀ c, FiniteProbability (S c) := fun c ↦
    (uniformOnFinset (S c) (hS c)).exponentialTilt (score c)
  let Gsub : ∀ c, Finset (S c) := fun c ↦
    guardSubtype (S c) G.guards
  let nu : ∀ c, FiniteProbability (S c) := fun c ↦
    (mu c).deleteGuards (Gsub c) (by
      simpa only [mu, Gsub, S, hS, score] using hsmall c)
  have hcellEq (c : Cell Head) :
      B.sampleData.cellFinset c =
        rawCell P I B.sampleData.n c \ G.guards := by
    calc
      B.sampleData.cellFinset c =
          (canonicalSampleData (W := B.sampleData.W)
            P I G hsep hremaining).cellFinset c :=
        congrArg (fun D : StructuredSampleData Head ↦ D.cellFinset c)
          hcanonical
      _ = rawCell P I B.sampleData.n c \ G.guards :=
        canonicalSampleData_cellFinset P I G hsep hremaining c
  have hfamilyEq :
      (fun c : Cell Head ↦ rawCell P I B.sampleData.n c \ G.guards) =
        B.sampleData.cellFinset := by
    funext c
    exact (hcellEq c).symm
  have hreindex (a b : ℕ) :
      (sigmaMixture weight nu).covariance
          (fun x ↦ valuation a (x.2 : ℕ))
          (fun x ↦ valuation b (x.2 : ℕ)) =
        (B.canonicalGuardedMediumReferenceLaw xi).probability.covariance
          (fun x ↦ valuation a
            ((B.canonicalGuardedMediumReferenceLaw xi).value x))
          (fun x ↦ valuation b
            ((B.canonicalGuardedMediumReferenceLaw xi).value x)) := by
    have hraw := sigmaMixture_deleteGuards_covariance_remaining_eq
      S (fun _c : Cell Head ↦ G.guards) hS hremaining score
        (by simpa only [S, hS, score] using hsmall) weight
        (fun _c m ↦ valuation a (m : ℕ))
        (fun _c m ↦ valuation b (m : ℕ))
    have hraw' : (sigmaMixture weight nu).covariance
          (fun x ↦ valuation a (x.2 : ℕ))
          (fun x ↦ valuation b (x.2 : ℕ)) =
        (sigmaMixture weight (fun c ↦
          (uniformOnFinset (S c \ G.guards) (hremaining c)).exponentialTilt
            (fun z ↦ score c (remainingEmbedding (S c) G.guards z)))).covariance
          (fun x ↦ valuation a (x.2 : ℕ))
          (fun x ↦ valuation b (x.2 : ℕ)) := by
      simpa only [S, hS, score, weight, mu, Gsub, nu,
        remainingEmbedding_value] using hraw
    have hremainingMedium :=
      sigmaMixture_tilt_covariance_eq_of_finset_family_eq
        (fun c : Cell Head ↦ S c \ G.guards)
        B.sampleData.cellFinset hfamilyEq hremaining
        B.sampleData.cell_nonempty
        (fun c z ↦ score c (remainingEmbedding (S c) G.guards z))
        (fun c ↦ sigmaCellScore (B.scaledMediumScore xi) c)
        (by
          intro c x y hxy
          change score c (remainingEmbedding (S c) G.guards x) =
            sigmaCellScore (B.scaledMediumScore xi) c y
          rw [B.sigmaCellScore_scaledMedium_eq_valuationScore xi c y]
          dsimp only [score]
          rw [remainingEmbedding_value, hxy])
        weight (valuation a) (valuation b)
    have htarget :
        (sigmaMixture weight (fun c ↦ B.cellMediumLaw xi c)).covariance
            (fun x ↦ valuation a (x.2 : ℕ))
            (fun x ↦ valuation b (x.2 : ℕ)) =
          (B.canonicalGuardedMediumReferenceLaw xi).probability.covariance
            (fun x ↦ valuation a
              ((B.canonicalGuardedMediumReferenceLaw xi).value x))
            (fun x ↦ valuation b
              ((B.canonicalGuardedMediumReferenceLaw xi).value x)) := by
      rfl
    exact hraw'.trans (hremainingMedium.trans htarget)
  have hreindexI (a b : ℕ) :
      (sigmaMixture weight nu).covariance
          (fun x ↦ divInd a (x.2 : ℕ))
          (fun x ↦ divInd b (x.2 : ℕ)) =
        (B.canonicalGuardedMediumReferenceLaw xi).probability.covariance
          (fun x ↦ divInd a
            ((B.canonicalGuardedMediumReferenceLaw xi).value x))
          (fun x ↦ divInd b
            ((B.canonicalGuardedMediumReferenceLaw xi).value x)) := by
    have hraw := sigmaMixture_deleteGuards_covariance_remaining_eq
      S (fun _c : Cell Head ↦ G.guards) hS hremaining score
        (by simpa only [S, hS, score] using hsmall) weight
        (fun _c m ↦ divInd a (m : ℕ))
        (fun _c m ↦ divInd b (m : ℕ))
    have hraw' : (sigmaMixture weight nu).covariance
          (fun x ↦ divInd a (x.2 : ℕ))
          (fun x ↦ divInd b (x.2 : ℕ)) =
        (sigmaMixture weight (fun c ↦
          (uniformOnFinset (S c \ G.guards) (hremaining c)).exponentialTilt
            (fun z ↦ score c (remainingEmbedding (S c) G.guards z)))).covariance
          (fun x ↦ divInd a (x.2 : ℕ))
          (fun x ↦ divInd b (x.2 : ℕ)) := by
      simpa only [S, hS, score, weight, mu, Gsub, nu,
        remainingEmbedding_value] using hraw
    have hremainingMedium :=
      sigmaMixture_tilt_covariance_eq_of_finset_family_eq
        (fun c : Cell Head ↦ S c \ G.guards)
        B.sampleData.cellFinset hfamilyEq hremaining
        B.sampleData.cell_nonempty
        (fun c z ↦ score c (remainingEmbedding (S c) G.guards z))
        (fun c ↦ sigmaCellScore (B.scaledMediumScore xi) c)
        (by
          intro c x y hxy
          change score c (remainingEmbedding (S c) G.guards x) =
            sigmaCellScore (B.scaledMediumScore xi) c y
          rw [B.sigmaCellScore_scaledMedium_eq_valuationScore xi c y]
          dsimp only [score]
          rw [remainingEmbedding_value, hxy])
        weight (divInd a) (divInd b)
    have htarget :
        (sigmaMixture weight (fun c ↦ B.cellMediumLaw xi c)).covariance
            (fun x ↦ divInd a (x.2 : ℕ))
            (fun x ↦ divInd b (x.2 : ℕ)) =
          (B.canonicalGuardedMediumReferenceLaw xi).probability.covariance
            (fun x ↦ divInd a
              ((B.canonicalGuardedMediumReferenceLaw xi).value x))
            (fun x ↦ divInd b
              ((B.canonicalGuardedMediumReferenceLaw xi).value x)) := by
      rfl
    exact hraw'.trans (hremainingMedium.trans htarget)
  have hmediumCorrection (q : BandPrime B.sampleData.n B.sampleData.W) :
      (B.canonicalGuardedMediumReferenceLaw xi).covVV p.1 q.1 -
          (B.canonicalGuardedMediumReferenceLaw xi).covII p.1 q.1 =
        PaperGuardCensus.powerCorrectionCovariance
          (sigmaMixture weight nu) (fun x ↦ (x.2 : ℕ)) p.1 q.1 := by
    rw [← powerCorrectionCovariance_eq_covVV_sub_covII
      (B.canonicalGuardedMediumReferenceLaw xi) p.1 q.1]
    unfold PaperGuardCensus.powerCorrectionCovariance
    rw [hreindex p.1 q.1, hreindexI p.1 q.1]
  have hrawCorrection (q : BandPrime B.sampleData.n B.sampleData.W) :
      (B.canonicalRawMediumReferenceLaw P I Cmax xi hC_le hS).covVV p.1 q.1 -
          (B.canonicalRawMediumReferenceLaw P I Cmax xi hC_le hS).covII p.1 q.1 =
        PaperGuardCensus.powerCorrectionCovariance
          (sigmaMixture weight mu) (fun x ↦ (x.2 : ℕ)) p.1 q.1 := by
    rw [← powerCorrectionCovariance_eq_covVV_sub_covII
      (B.canonicalRawMediumReferenceLaw P I Cmax xi hC_le hS) p.1 q.1]
    rfl
  calc
    ∑ q : BandPrime B.sampleData.n B.sampleData.W,
        |((B.canonicalGuardedMediumReferenceLaw xi).covVV p.1 q.1 -
            (B.canonicalGuardedMediumReferenceLaw xi).covII p.1 q.1) -
          ((B.canonicalRawMediumReferenceLaw P I Cmax xi hC_le hS).covVV p.1 q.1 -
            (B.canonicalRawMediumReferenceLaw P I Cmax xi hC_le hS).covII p.1 q.1)| =
      ∑ q : BandPrime B.sampleData.n B.sampleData.W,
        |PaperGuardCensus.powerCorrectionCovariance
            (sigmaMixture weight nu) (fun x ↦ (x.2 : ℕ)) p.1 q.1 -
          PaperGuardCensus.powerCorrectionCovariance
            (sigmaMixture weight mu) (fun x ↦ (x.2 : ℕ)) p.1 q.1| := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [hmediumCorrection q, hrawCorrection q]
    _ ≤ PaperGuardCensus.guardPowerCorrectionRowError K d := by
      simpa only [S, mu, nu, Gsub, hS, score, weight] using hguard

/-- The guard perturbation needed by the canonical raw cells is a fixed
multiple of the ledger census ratio. -/
def canonicalGuardPerturbationConstant
    (P : Head → HeadPattern.Pattern) (I : PhysicalIntervals)
    (Kscore : ℝ) : ℝ :=
  ∑ c : Cell Head,
    8 * Real.exp (2 * Kscore) /
      PaperScaleMarkedCell.paperCellDensity
        (P c.1) (I.lower c.2) (I.upper c.2)

omit [DecidableEq Head] in theorem canonicalGuardPerturbationConstant_nonneg
    (P : Head → HeadPattern.Pattern) (I : PhysicalIntervals)
    (Kscore : ℝ) :
    0 ≤ canonicalGuardPerturbationConstant P I Kscore := by
  unfold canonicalGuardPerturbationConstant
  apply Finset.sum_nonneg
  intro c hc
  exact div_nonneg (mul_nonneg (by norm_num) (Real.exp_pos _).le)
    (PaperScaleMarkedCell.paperCellDensity_pos
      (P c.1) (I.lower_lt_upper c.2)).le

/-- The literal weighted guard-row majorant.  `Cenv * L` is the total
valuation envelope and `D * censusRatioMajorant` is the conditional guard
normalization loss. -/
def guardPowerCorrectionWeightedMajorant
    (Cprom Cbank : ℕ) (Cenv D : ℝ) (n : ℕ) : ℝ :=
  (yNat n : ℝ) *
    PaperGuardCensus.guardPowerCorrectionRowError
      (Cenv * Scale.L n)
      (D * PaperGuardCensus.censusRatioMajorant Cprom Cbank n)

/-- The actual medium-prime score on a canonical unguarded raw cell has a
fixed-box bound independent of `n`, of the cell, and of the number of active
prime bands.  This is proved directly from the total valuation logarithm;
no probabilistic input is used. -/
theorem abs_canonicalRaw_mediumScore_le
    [Nonempty Head]
    (P : Head → HeadPattern.Pattern) (I : PhysicalIntervals)
    (Cmax : ℝ) (hCmax : 1 ≤ Cmax)
    (hupperMax : ∀ sigma, I.upper sigma ≤ Cmax)
    (xi : B.ParamSpace) (hW : 1 < B.sampleData.W)
    {Acoef : ℝ} (hAcoef : 0 ≤ Acoef)
    (heta : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |B.effectivePrimeCoefficient xi p| ≤ Acoef)
    (c : Cell Head) (m : rawCell P I B.sampleData.n c) :
    |valuationScore
        (primeBand B.sampleData.n B.sampleData.W)
        (B.effectiveNatCoefficient xi) B.L (m : ℕ)| ≤
      Acoef * PaperStatisticNorm.valuationLogCoefficient
        Cmax B.sampleData.W := by
  have hmpos : 0 < (m : ℕ) :=
    pos_of_mem_smoothInterval (mem_structuredCell.mp m.property).1
  have hmhi : (m : ℕ) ≤
      physicalBound (I.upper c.2) B.sampleData.n :=
    (mem_smoothInterval.mp (mem_structuredCell.mp m.property).1).2.1
  have hmC : (m : ℕ) ≤ physicalBound Cmax B.sampleData.n :=
    hmhi.trans (FixedFiniteMixtureFullUniform.physicalBound_mono
      (hupperMax c.2) B.sampleData.n)
  have hpW : ∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
      B.sampleData.W ≤ p := by
    intro p hp
    exact (cutoff_lt_of_mem_primeBand hp).le
  have hetaNat : ∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
      |B.effectiveNatCoefficient xi p| ≤ Acoef := by
    intro p hp
    rw [B.effectiveNatCoefficient_of_mem xi hp]
    exact heta ⟨p, hp⟩
  have hraw := ValuationTiltCell.abs_valuationScore_le_log_ratio
    (primeBand B.sampleData.n B.sampleData.W)
    (B.effectiveNatCoefficient xi) hmpos hmC hW hpW hAcoef B.L_pos hetaNat
  have hlogW : 0 < Real.log (B.sampleData.W : ℝ) :=
    Real.log_pos (by exact_mod_cast hW)
  have hcoef : 0 ≤ Acoef / B.L := div_nonneg hAcoef B.L_pos.le
  calc
    |valuationScore
        (primeBand B.sampleData.n B.sampleData.W)
        (B.effectiveNatCoefficient xi) B.L (m : ℕ)| ≤
      (Acoef / B.L) *
        (Real.log (physicalBound Cmax B.sampleData.n : ℝ) /
          Real.log (B.sampleData.W : ℝ)) := hraw
    _ ≤ (Acoef / B.L) *
        ((PaperStatisticNorm.physicalLogCoefficient Cmax * B.L) /
          Real.log (B.sampleData.W : ℝ)) := by
      exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right
          (PaperStatisticNorm.BridgeData.log_physicalBound_le B hCmax)
          hlogW.le) hcoef
    _ = Acoef * PaperStatisticNorm.valuationLogCoefficient
          Cmax B.sampleData.W := by
      unfold PaperStatisticNorm.valuationLogCoefficient
      field_simp [B.L_pos.ne', hlogW.ne']

/-- Elementary physical-log discharge of the logarithmic valuation envelope.
The constant is the same fixed-cutoff coefficient as in the score bound. -/
theorem valuationEnvelope_le_valuationLogCoefficient_mul_L
    (I : PhysicalIntervals) (Cmax : ℝ)
    (hupperOne : ∀ sigma, 1 ≤ I.upper sigma)
    (hupperMax : ∀ sigma, I.upper sigma ≤ Cmax)
    (hW : 1 < B.sampleData.W) (c : Cell Head) :
    valuationEnvelope I B.sampleData.n B.sampleData.W c ≤
      PaperStatisticNorm.valuationLogCoefficient Cmax B.sampleData.W * B.L := by
  have hCmax : 1 ≤ Cmax :=
    (hupperOne c.2).trans (hupperMax c.2)
  have hnpos : 0 < B.sampleData.n := Nat.zero_lt_of_lt B.n_gt_one
  have hnR : (0 : ℝ) < (B.sampleData.n : ℝ) := by exact_mod_cast hnpos
  have hupperPos : 0 < I.upper c.2 :=
    zero_lt_one.trans_le (hupperOne c.2)
  have hphysicalPos : (0 : ℝ) <
      physicalBound (I.upper c.2) B.sampleData.n := by
    have hnle : B.sampleData.n ≤
        physicalBound (I.upper c.2) B.sampleData.n := by
      unfold physicalBound
      apply Nat.le_floor
      exact_mod_cast (show (B.sampleData.n : ℝ) ≤
        I.upper c.2 * (B.sampleData.n : ℝ) by
          nlinarith [hnR.le, hupperOne c.2])
    exact_mod_cast hnpos.trans_le hnle
  have hphysicalMono :
      physicalBound (I.upper c.2) B.sampleData.n ≤
        physicalBound Cmax B.sampleData.n :=
    FixedFiniteMixtureFullUniform.physicalBound_mono
      (hupperMax c.2) B.sampleData.n
  have hlogMono :
      Real.log (physicalBound (I.upper c.2) B.sampleData.n : ℝ) ≤
        Real.log (physicalBound Cmax B.sampleData.n : ℝ) :=
    Real.log_le_log hphysicalPos (by exact_mod_cast hphysicalMono)
  have hlogW : 0 < Real.log (B.sampleData.W : ℝ) :=
    Real.log_pos (by exact_mod_cast hW)
  calc
    valuationEnvelope I B.sampleData.n B.sampleData.W c =
        Real.log (physicalBound (I.upper c.2) B.sampleData.n : ℝ) /
          Real.log (B.sampleData.W : ℝ) := rfl
    _ ≤ Real.log (physicalBound Cmax B.sampleData.n : ℝ) /
          Real.log (B.sampleData.W : ℝ) :=
      div_le_div_of_nonneg_right hlogMono hlogW.le
    _ ≤ (PaperStatisticNorm.physicalLogCoefficient Cmax * B.L) /
          Real.log (B.sampleData.W : ℝ) :=
      div_le_div_of_nonneg_right
        (PaperStatisticNorm.BridgeData.log_physicalBound_le B hCmax)
        hlogW.le
    _ = PaperStatisticNorm.valuationLogCoefficient Cmax
          B.sampleData.W * B.L := by
      unfold PaperStatisticNorm.valuationLogCoefficient
      ring

/-- Fully concrete finite-`n` guard specialization of the prime-power row.

The hypotheses are precisely the estimates supplied by the canonical raw
cells: a pointwise bound for the actual medium score, the literal half-mass
census inequality, the proved raw-cell density, and a logarithmic valuation
envelope.  The conclusion keeps the actual post-tilt component weights.  In
particular, no comparison with an arbitrarily chosen mixture is hidden in the
statement. -/
theorem weighted_sum_abs_physicalMediumReference_powerCorrection_sub_canonicalRaw_le
    [Nonempty Head]
    (P : Head → HeadPattern.Pattern) (I : PhysicalIntervals)
    (Cmax : ℝ) {Cprom Cbank : ℕ}
    (G : Ledger B.sampleData.n Cprom Cbank)
    (hsep : physicalBound (I.upper .minus) B.sampleData.n <
      physicalBound (I.lower .plus) B.sampleData.n)
    (hremaining : ∀ c : Cell Head,
      (rawCell P I B.sampleData.n c \ G.guards).Nonempty)
    (hcanonical : B.sampleData =
      canonicalSampleData (W := B.sampleData.W) P I G hsep hremaining)
    (xi : B.ParamSpace)
    (hC_le : ∀ sigma, I.upper sigma ≤ Cmax)
    (hW : 1 < B.sampleData.W)
    {Kscore Cenv : ℝ} (hCenv : 0 ≤ Cenv)
    (hscore : ∀ c : Cell Head,
      ∀ m : rawCell P I B.sampleData.n c,
        |valuationScore
          (primeBand B.sampleData.n B.sampleData.W)
          (B.effectiveNatCoefficient xi) B.L (m : ℕ)| ≤ Kscore)
    (hsmallCensus : ∀ c : Cell Head,
      Real.exp (2 * Kscore) * (G.guards.card : ℝ) /
        ((rawCell P I B.sampleData.n c).card : ℝ) ≤ (1 : ℝ) / 2)
    (hdensity : ∀ c : Cell Head,
      PaperScaleMarkedCell.paperCellDensity
          (P c.1) (I.lower c.2) (I.upper c.2) *
          (B.sampleData.n : ℝ) / 2 ≤
        (rawCell P I B.sampleData.n c).card)
    (hEnvelope : ∀ c : Cell Head,
      valuationEnvelope I B.sampleData.n B.sampleData.W c ≤
        Cenv * Scale.L B.sampleData.n)
    (p : BandPrime B.sampleData.n B.sampleData.W) :
    (p.1 : ℝ) *
      ∑ q : BandPrime B.sampleData.n B.sampleData.W,
        |((B.canonicalGuardedMediumReferenceLaw xi).covVV p.1 q.1 -
            (B.canonicalGuardedMediumReferenceLaw xi).covII p.1 q.1) -
          ((B.canonicalRawMediumReferenceLaw P I Cmax xi hC_le
              (fun c ↦ (hremaining c).mono Finset.sdiff_subset)).covVV p.1 q.1 -
            (B.canonicalRawMediumReferenceLaw P I Cmax xi hC_le
              (fun c ↦ (hremaining c).mono Finset.sdiff_subset)).covII p.1 q.1)| ≤
      guardPowerCorrectionWeightedMajorant Cprom Cbank Cenv
        (canonicalGuardPerturbationConstant P I Kscore) B.sampleData.n := by
  let census := PaperGuardCensus.censusRatioMajorant
    Cprom Cbank B.sampleData.n
  let Dguard := canonicalGuardPerturbationConstant P I Kscore
  let hS : ∀ c : Cell Head, (rawCell P I B.sampleData.n c).Nonempty :=
    fun c ↦ (hremaining c).mono Finset.sdiff_subset
  let score : ∀ c : Cell Head, rawCell P I B.sampleData.n c → ℝ :=
    fun _ m ↦ valuationScore
      (primeBand B.sampleData.n B.sampleData.W)
      (B.effectiveNatCoefficient xi) B.L (m : ℕ)
  have hn : 1 ≤ B.sampleData.n := B.n_gt_one.le
  have hnpos : 0 < B.sampleData.n := Nat.zero_lt_of_lt B.n_gt_one
  have hcensus0 : 0 ≤ census := by
    dsimp only [census]
    unfold PaperGuardCensus.censusRatioMajorant
    have hL0 : 0 ≤ Scale.L B.sampleData.n :=
      Real.log_nonneg (by exact_mod_cast hn)
    have hcoef : 0 ≤ (Cprom : ℝ) +
        3 * (Cbank : ℝ) * (Scale.L B.sampleData.n + 2) := by
      positivity
    exact div_nonneg
      (mul_nonneg hcoef (Scale.y_pos hnpos).le) (by positivity)
  have hDguard0 : 0 ≤ Dguard := by
    simpa only [Dguard] using
      canonicalGuardPerturbationConstant_nonneg P I Kscore
  have hsmall : ∀ c : Cell Head,
      (((uniformOnFinset (rawCell P I B.sampleData.n c) (hS c)).exponentialTilt
        (score c)).guardMass
        (guardSubtype (rawCell P I B.sampleData.n c) G.guards) < 1) := by
    intro c
    let mu := (uniformOnFinset (rawCell P I B.sampleData.n c) (hS c)).exponentialTilt
      (score c)
    let guards := guardSubtype (rawCell P I B.sampleData.n c) G.guards
    have hmass : mu.guardMass guards ≤
        Real.exp (2 * Kscore) * (G.guards.card : ℝ) /
          ((rawCell P I B.sampleData.n c).card : ℝ) := by
      simpa only [mu, guards, score, hS] using
        tilted_uniform_guardMass_le
          (rawCell P I B.sampleData.n c) G.guards (hS c) (score c)
          Kscore (by simpa only [score] using hscore c)
    have hhalf : mu.guardMass guards ≤ (1 : ℝ) / 2 :=
      hmass.trans (hsmallCensus c)
    exact hhalf.trans_lt (by norm_num)
  have hperturb : ∀ c : Cell Head,
      (((uniformOnFinset (rawCell P I B.sampleData.n c) (hS c)).exponentialTilt
        (score c)).guardPerturbation
        (guardSubtype (rawCell P I B.sampleData.n c) G.guards) ≤
          Dguard * census) := by
    intro c
    let S := rawCell P I B.sampleData.n c
    let mu := (uniformOnFinset S (hS c)).exponentialTilt (score c)
    let guards := guardSubtype S G.guards
    let density := PaperScaleMarkedCell.paperCellDensity
      (P c.1) (I.lower c.2) (I.upper c.2)
    have hdensityPos : 0 < density := by
      exact PaperScaleMarkedCell.paperCellDensity_pos
        (P c.1) (I.lower_lt_upper c.2)
    have hratio : (G.guards.card : ℝ) / (S.card : ℝ) ≤
        2 * census / density := by
      simpa only [S, census] using
        guard_card_div_rawCell_le P I G c hn (hdensity c)
    have hmass : mu.guardMass guards ≤
        Real.exp (2 * Kscore) * (G.guards.card : ℝ) / (S.card : ℝ) := by
      simpa only [mu, guards, S, score, hS] using
        tilted_uniform_guardMass_le S G.guards (hS c) (score c)
          Kscore (by simpa only [score] using hscore c)
    have hhalf : mu.guardMass guards ≤ (1 : ℝ) / 2 := by
      exact hmass.trans (by simpa only [S] using hsmallCensus c)
    have hperturbMass :=
      mu.guardPerturbation_le_four_mul_guardMass guards hhalf
    have hcellConstant :
        8 * Real.exp (2 * Kscore) / density ≤ Dguard := by
      have hsingle :
          8 * Real.exp (2 * Kscore) /
              PaperScaleMarkedCell.paperCellDensity
                (P c.1) (I.lower c.2) (I.upper c.2) ≤
            ∑ c' : Cell Head,
              8 * Real.exp (2 * Kscore) /
                PaperScaleMarkedCell.paperCellDensity
                  (P c'.1) (I.lower c'.2) (I.upper c'.2) :=
        Finset.single_le_sum
          (fun c' hc' ↦ div_nonneg
            (mul_nonneg (by norm_num) (Real.exp_pos _).le)
            (PaperScaleMarkedCell.paperCellDensity_pos
              (P c'.1) (I.lower_lt_upper c'.2)).le)
          (Finset.mem_univ c)
      simpa only [Dguard, canonicalGuardPerturbationConstant, density] using hsingle
    have hmassRatio : mu.guardMass guards ≤
        Real.exp (2 * Kscore) * (2 * census / density) := by
      calc
        mu.guardMass guards ≤
            Real.exp (2 * Kscore) * (G.guards.card : ℝ) /
              (S.card : ℝ) := hmass
        _ = Real.exp (2 * Kscore) *
              ((G.guards.card : ℝ) / (S.card : ℝ)) := by ring
        _ ≤ Real.exp (2 * Kscore) * (2 * census / density) :=
          mul_le_mul_of_nonneg_left hratio (Real.exp_pos _).le
    calc
      mu.guardPerturbation guards ≤ 4 * mu.guardMass guards := hperturbMass
      _ ≤ 4 * (Real.exp (2 * Kscore) * (2 * census / density)) :=
        mul_le_mul_of_nonneg_left hmassRatio (by norm_num)
      _ = (8 * Real.exp (2 * Kscore) / density) * census := by ring
      _ ≤ Dguard * census :=
        mul_le_mul_of_nonneg_right hcellConstant hcensus0
  have hrow :=
    B.sum_abs_physicalMediumReference_powerCorrection_sub_canonicalRaw_le
      P I Cmax G hsep hremaining hcanonical xi hC_le hW
      (K := Cenv * Scale.L B.sampleData.n) (d := Dguard * census)
      (mul_nonneg hCenv B.L_pos.le) (mul_nonneg hDguard0 hcensus0)
      hEnvelope
      (by simpa only [hS, score] using hsmall)
      (by simpa only [hS, score] using hperturb) p
  have hpY : (p.1 : ℝ) ≤ (yNat B.sampleData.n : ℝ) := by
    exact_mod_cast le_yNat_of_mem_primeBand p.2
  have hsum0 : 0 ≤
      ∑ q : BandPrime B.sampleData.n B.sampleData.W,
        |((B.canonicalGuardedMediumReferenceLaw xi).covVV p.1 q.1 -
            (B.canonicalGuardedMediumReferenceLaw xi).covII p.1 q.1) -
          ((B.canonicalRawMediumReferenceLaw P I Cmax xi hC_le hS).covVV p.1 q.1 -
            (B.canonicalRawMediumReferenceLaw P I Cmax xi hC_le hS).covII p.1 q.1)| :=
    Finset.sum_nonneg fun q hq ↦ abs_nonneg _
  calc
    (p.1 : ℝ) *
        ∑ q : BandPrime B.sampleData.n B.sampleData.W,
          |((B.canonicalGuardedMediumReferenceLaw xi).covVV p.1 q.1 -
              (B.canonicalGuardedMediumReferenceLaw xi).covII p.1 q.1) -
            ((B.canonicalRawMediumReferenceLaw P I Cmax xi hC_le hS).covVV p.1 q.1 -
              (B.canonicalRawMediumReferenceLaw P I Cmax xi hC_le hS).covII p.1 q.1)| ≤
      (yNat B.sampleData.n : ℝ) *
        ∑ q : BandPrime B.sampleData.n B.sampleData.W,
          |((B.canonicalGuardedMediumReferenceLaw xi).covVV p.1 q.1 -
              (B.canonicalGuardedMediumReferenceLaw xi).covII p.1 q.1) -
            ((B.canonicalRawMediumReferenceLaw P I Cmax xi hC_le hS).covVV p.1 q.1 -
              (B.canonicalRawMediumReferenceLaw P I Cmax xi hC_le hS).covII p.1 q.1)| :=
        mul_le_mul_of_nonneg_right hpY hsum0
    _ ≤ (yNat B.sampleData.n : ℝ) *
        PaperGuardCensus.guardPowerCorrectionRowError
          (Cenv * Scale.L B.sampleData.n) (Dguard * census) :=
      mul_le_mul_of_nonneg_left hrow (by positivity)
    _ = guardPowerCorrectionWeightedMajorant Cprom Cbank Cenv Dguard
        B.sampleData.n := by
      rfl

/-- Eventual canonical constructor specialization with every analytic input
to the finite guard theorem discharged.

For a fixed coefficient box and fixed physical cells, this theorem chooses a
single threshold independent of the later band partition, bridge data, tilt
point, and prime row.  Above that threshold the raw-cell density and the
half-mass inequality come from the proved ledger census; the score and
valuation-envelope bounds are the two elementary logarithmic estimates
above.  Thus the only hypotheses at the call site are exact structural
identification with `canonicalSampleData` and the genuine coefficient box. -/
theorem exists_eventually_canonicalGuardPowerCorrection_reference_bound
    [Nonempty Head]
    (P : Head → HeadPattern.Pattern) (I : PhysicalIntervals)
    (Cmax : ℝ)
    (hupperOne : ∀ sigma, 1 ≤ I.upper sigma)
    (hupperMax : ∀ sigma, I.upper sigma ≤ Cmax)
    (Cprom Cbank : ℕ)
    (ledger : ∀ n, Ledger n Cprom Cbank)
    (W : ℕ) (hW : 1 < W)
    (Acoef : ℝ) (hAcoef : 0 ≤ Acoef) :
    let Cenv := PaperStatisticNorm.valuationLogCoefficient Cmax W
    let Kscore := Acoef * Cenv
    let Dguard := canonicalGuardPerturbationConstant P I Kscore
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
          ∀ p : BandPrime B.sampleData.n B.sampleData.W,
            (p.1 : ℝ) *
              ∑ q : BandPrime B.sampleData.n B.sampleData.W,
                |((B.canonicalGuardedMediumReferenceLaw xi).covVV p.1 q.1 -
                    (B.canonicalGuardedMediumReferenceLaw xi).covII p.1 q.1) -
                  ((B.canonicalRawMediumReferenceLaw P I Cmax xi hupperMax
                      (fun c ↦ (hremaining c).mono
                        Finset.sdiff_subset)).covVV p.1 q.1 -
                    (B.canonicalRawMediumReferenceLaw P I Cmax xi hupperMax
                      (fun c ↦ (hremaining c).mono
                        Finset.sdiff_subset)).covII p.1 q.1)| ≤
              guardPowerCorrectionWeightedMajorant Cprom Cbank Cenv
                Dguard B.sampleData.n := by
  dsimp only
  let Cenv := PaperStatisticNorm.valuationLogCoefficient Cmax W
  let Kscore := Acoef * Cenv
  let Dguard := canonicalGuardPerturbationConstant P I Kscore
  have hCmax : 1 ≤ Cmax :=
    (hupperOne .minus).trans (hupperMax .minus)
  have hCenv : 0 ≤ Cenv := by
    simpa only [Cenv] using
      PaperStatisticNorm.valuationLogCoefficient_nonneg hCmax hW
  have hdensityEvent := eventually_rawCell_density P I
  have hsmallEvent :=
    GuardSquarefreeErrorRate.eventually_exp_two_mul_guardRatio_rawCell_le_half
      P I Cprom Cbank ledger Kscore
  obtain ⟨Ndensity, hNdensity⟩ := Filter.eventually_atTop.1 hdensityEvent
  obtain ⟨Nsmall, hNsmall⟩ := Filter.eventually_atTop.1 hsmallEvent
  refine ⟨max Ndensity Nsmall, ?_⟩
  intro Band _instBand _instBandDec B xi hN hBW hsep hremaining
    hcanonical heta p
  have hNdensity' : Ndensity ≤ B.sampleData.n :=
    (Nat.le_max_left _ _).trans hN
  have hNsmall' : Nsmall ≤ B.sampleData.n :=
    (Nat.le_max_right _ _).trans hN
  have hdensity := hNdensity B.sampleData.n hNdensity'
  have hsmallCensus := hNsmall B.sampleData.n hNsmall'
  have hWBridge : 1 < B.sampleData.W := by
    simpa only [hBW] using hW
  have hscore : ∀ c : Cell Head,
      ∀ m : rawCell P I B.sampleData.n c,
        |valuationScore
          (primeBand B.sampleData.n B.sampleData.W)
          (B.effectiveNatCoefficient xi) B.L (m : ℕ)| ≤ Kscore := by
    intro c m
    have hraw := B.abs_canonicalRaw_mediumScore_le
      P I Cmax hCmax hupperMax xi hWBridge hAcoef heta c m
    simpa only [Kscore, Cenv, hBW] using hraw
  have hEnvelope : ∀ c : Cell Head,
      valuationEnvelope I B.sampleData.n B.sampleData.W c ≤
        Cenv * Scale.L B.sampleData.n := by
    intro c
    have hraw := B.valuationEnvelope_le_valuationLogCoefficient_mul_L
      I Cmax hupperOne hupperMax hWBridge c
    simpa only [Cenv, hBW, BridgeData.L, Scale.L] using hraw
  exact B.weighted_sum_abs_physicalMediumReference_powerCorrection_sub_canonicalRaw_le
    P I Cmax (ledger B.sampleData.n) hsep hremaining hcanonical xi
    hupperMax hWBridge hCenv hscore hsmallCensus hdensity hEnvelope p

private theorem guardPowerCorrectionRowError_eq (K d : ℝ) :
    PaperGuardCensus.guardPowerCorrectionRowError K d =
      (K ^ 2 + K) * (7 * d + 2 * d ^ 2) := by
  unfold PaperGuardCensus.guardPowerCorrectionRowError
  ring

private theorem tendsto_L_sq_div_y_zero :
    Tendsto (fun n : ℕ ↦ Scale.L n ^ 2 / ArithmeticModel.y n)
      atTop (nhds 0) := by
  have hreal : Tendsto
      (fun x : ℝ ↦ Real.log x ^ (2 : ℝ) / x ^ (2 / 9 : ℝ))
        atTop (nhds 0) :=
    (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (by norm_num : (0 : ℝ) < 2 / 9))
      |>.tendsto_div_nhds_zero
  have hnat := hreal.comp tendsto_natCast_atTop_atTop
  change Tendsto
    (fun n : ℕ ↦ Real.log (n : ℝ) ^ (2 : ℝ) /
      (n : ℝ) ^ (2 / 9 : ℝ)) atTop (nhds 0) at hnat
  simpa [Scale.L, ArithmeticModel.y, Real.rpow_natCast] using hnat

private theorem eventually_L_sq_le_y :
    ∀ᶠ n : ℕ in atTop, Scale.L n ^ 2 ≤ ArithmeticModel.y n := by
  have hratio := tendsto_L_sq_div_y_zero.eventually
    (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hratio, eventually_gt_atTop 0] with n hratio hn
  have hy : 0 < ArithmeticModel.y n := Scale.y_pos hn
  exact (div_le_iff₀ hy).mp hratio |>.trans_eq (one_mul _)

/-- The `p ≤ y` guard loss is still negligible after the moving-low
factor `log L`; equivalently it is `o(1 / log L)`, the scale of the low
arithmetic center. -/
theorem tendsto_guardPowerCorrectionWeightedMajorant_mul_logL_zero
    (Cprom Cbank : ℕ) {Cenv D : ℝ}
    (hCenv : 0 ≤ Cenv) (hD : 0 ≤ D) :
    Tendsto (fun n : ℕ ↦
      guardPowerCorrectionWeightedMajorant Cprom Cbank Cenv D n *
        Real.log (Scale.L n)) atTop (nhds 0) := by
  let constant := 9 * D * (Cenv ^ 2 + Cenv)
  have hconstant : 0 ≤ constant := by
    dsimp only [constant]
    positivity
  have hdT : Tendsto (fun n : ℕ ↦
      D * PaperGuardCensus.censusRatioMajorant Cprom Cbank n)
      atTop (nhds 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul
      (GuardSquarefreeErrorRate.tendsto_censusRatioMajorant_zero
        Cprom Cbank)
  have hdle : ∀ᶠ n : ℕ in atTop,
      D * PaperGuardCensus.censusRatioMajorant Cprom Cbank n ≤ 1 :=
    hdT.eventually (eventually_le_nhds (by norm_num))
  have hLTop : Tendsto Scale.L atTop atTop := by
    simpa only [Scale.L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hLge : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ Scale.L n :=
    hLTop.eventually (eventually_ge_atTop 1)
  have hlog0 : ∀ᶠ n : ℕ in atTop, 0 ≤ Real.log (Scale.L n) :=
    hLge.mono fun n hn ↦ Real.log_nonneg hn
  have hupper :=
    GuardSquarefreeErrorRate.tendsto_guardRateMajorant_mul_logL_zero
      Cprom Cbank constant
  refine squeeze_zero' ?_ ?_ hupper
  · filter_upwards [eventually_gt_atTop 0, hlog0] with n hn hlog
    have hLn : 0 ≤ Scale.L n := Real.log_nonneg (by exact_mod_cast hn)
    have hcensus : 0 ≤
        PaperGuardCensus.censusRatioMajorant Cprom Cbank n := by
      unfold PaperGuardCensus.censusRatioMajorant
      have hcoef : 0 ≤ (Cprom : ℝ) +
          3 * (Cbank : ℝ) * (Scale.L n + 2) := by positivity
      exact div_nonneg
        (mul_nonneg hcoef (Scale.y_pos hn).le) (by positivity)
    exact mul_nonneg
      (mul_nonneg (by positivity)
        (PaperGuardCensus.guardPowerCorrectionRowError_nonneg
          (mul_nonneg hCenv hLn)
          (mul_nonneg hD hcensus))) hlog
  · filter_upwards [eventually_gt_atTop 0, hdle, hLge,
      eventually_L_sq_le_y, hlog0] with n hn hdOne hLn hLsq hlog
    let census := PaperGuardCensus.censusRatioMajorant Cprom Cbank n
    let d := D * census
    let K := Cenv * Scale.L n
    have hcensus : 0 ≤ census := by
      dsimp only [census]
      unfold PaperGuardCensus.censusRatioMajorant
      have hL0 : 0 ≤ Scale.L n := Real.log_nonneg (by exact_mod_cast hn)
      have hcoef : 0 ≤ (Cprom : ℝ) +
          3 * (Cbank : ℝ) * (Scale.L n + 2) := by positivity
      exact div_nonneg
        (mul_nonneg hcoef (Scale.y_pos hn).le) (by positivity)
    have hd0 : 0 ≤ d := mul_nonneg hD hcensus
    have hK0 : 0 ≤ K := mul_nonneg hCenv (zero_le_one.trans hLn)
    have hdpoly : 7 * d + 2 * d ^ 2 ≤ 9 * d := by
      nlinarith [mul_nonneg hd0 (sub_nonneg.mpr hdOne)]
    have hKpoly : K ^ 2 + K ≤
        (Cenv ^ 2 + Cenv) * Scale.L n ^ 2 := by
      dsimp only [K]
      have haux : 0 ≤ Cenv * Scale.L n * (Scale.L n - 1) :=
        mul_nonneg (mul_nonneg hCenv (zero_le_one.trans hLn))
          (sub_nonneg.mpr hLn)
      nlinarith
    have herror :
        PaperGuardCensus.guardPowerCorrectionRowError K d ≤
          constant * census * Scale.L n ^ 2 := by
      rw [guardPowerCorrectionRowError_eq]
      calc
        (K ^ 2 + K) * (7 * d + 2 * d ^ 2) ≤
            (K ^ 2 + K) * (9 * d) :=
          mul_le_mul_of_nonneg_left hdpoly (add_nonneg (sq_nonneg K) hK0)
        _ ≤ ((Cenv ^ 2 + Cenv) * Scale.L n ^ 2) * (9 * d) :=
          mul_le_mul_of_nonneg_right hKpoly (mul_nonneg (by norm_num) hd0)
        _ = constant * census * Scale.L n ^ 2 := by
          dsimp only [constant, d, census]
          ring
    have hyNat : (yNat n : ℝ) ≤ ArithmeticModel.y n :=
      Nat.floor_le (Scale.y_pos hn).le
    have herror0 : 0 ≤
        PaperGuardCensus.guardPowerCorrectionRowError K d :=
      PaperGuardCensus.guardPowerCorrectionRowError_nonneg hK0 hd0
    have hbase :
        (yNat n : ℝ) *
            PaperGuardCensus.guardPowerCorrectionRowError K d ≤
          constant * (census * ArithmeticModel.y n ^ 2) := by
      calc
        (yNat n : ℝ) *
            PaperGuardCensus.guardPowerCorrectionRowError K d ≤
          ArithmeticModel.y n *
            PaperGuardCensus.guardPowerCorrectionRowError K d :=
          mul_le_mul_of_nonneg_right hyNat herror0
        _ ≤ ArithmeticModel.y n *
            (constant * census * Scale.L n ^ 2) :=
          mul_le_mul_of_nonneg_left herror (Scale.y_pos hn).le
        _ ≤ ArithmeticModel.y n *
            (constant * census * ArithmeticModel.y n) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hLsq
              (mul_nonneg hconstant hcensus))
            (Scale.y_pos hn).le
        _ = constant * (census * ArithmeticModel.y n ^ 2) := by ring
    have hbaseLog := mul_le_mul_of_nonneg_right hbase hlog
    simpa only [guardPowerCorrectionWeightedMajorant, K, d, census,
      constant, mul_assoc] using hbaseLog

/-- Literal sharp relative form of the preceding rate.  Whenever the
moving low-cell center has the paper's lower scale
`alpha₀(n) ≥ c / log L(n)` with a fixed `c > 0`, the weighted canonical
guard row is `o(alpha₀)`.  This statement is deliberately independent of
any choice of continuum gauge. -/
theorem tendsto_guardPowerCorrectionWeightedMajorant_div_lowCenter_zero
    (Cprom Cbank : ℕ) {Cenv D c : ℝ}
    (hCenv : 0 ≤ Cenv) (hD : 0 ≤ D) (hc : 0 < c)
    (alpha₀ : ℕ → ℝ)
    (halpha₀ : ∀ᶠ n : ℕ in atTop,
      c / Real.log (Scale.L n) ≤ alpha₀ n) :
    Tendsto (fun n : ℕ ↦
      guardPowerCorrectionWeightedMajorant Cprom Cbank Cenv D n /
        alpha₀ n) atTop (nhds 0) := by
  have hmain :=
    tendsto_guardPowerCorrectionWeightedMajorant_mul_logL_zero
      Cprom Cbank hCenv hD
  have hupper : Tendsto (fun n : ℕ ↦
      (guardPowerCorrectionWeightedMajorant Cprom Cbank Cenv D n *
        Real.log (Scale.L n)) / c) atTop (nhds 0) := by
    simpa only [zero_div] using hmain.div_const c
  have hLTop : Tendsto Scale.L atTop atTop := by
    simpa only [Scale.L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlogPos : ∀ᶠ n : ℕ in atTop, 0 < Real.log (Scale.L n) := by
    filter_upwards [hLTop.eventually (eventually_gt_atTop 1)] with n hn
    exact Real.log_pos hn
  refine squeeze_zero' ?_ ?_ hupper
  · filter_upwards [eventually_gt_atTop 1, hlogPos, halpha₀] with
        n hn hlog halpha
    have hLn : 0 ≤ Scale.L n :=
      Real.log_nonneg (by exact_mod_cast (Nat.le_of_lt hn))
    have hcensus : 0 ≤
        PaperGuardCensus.censusRatioMajorant Cprom Cbank n := by
      unfold PaperGuardCensus.censusRatioMajorant
      have hcoef : 0 ≤ (Cprom : ℝ) +
          3 * (Cbank : ℝ) * (Scale.L n + 2) := by positivity
      exact div_nonneg
        (mul_nonneg hcoef (Scale.y_pos (by omega : 0 < n)).le)
        (by positivity)
    have hmajor : 0 ≤
        guardPowerCorrectionWeightedMajorant Cprom Cbank Cenv D n := by
      unfold guardPowerCorrectionWeightedMajorant
      exact mul_nonneg (by positivity)
        (PaperGuardCensus.guardPowerCorrectionRowError_nonneg
          (mul_nonneg hCenv hLn) (mul_nonneg hD hcensus))
    have halphaPos : 0 < alpha₀ n :=
      (div_pos hc hlog).trans_le halpha
    exact div_nonneg hmajor halphaPos.le
  · filter_upwards [eventually_gt_atTop 1, hlogPos, halpha₀] with
        n hn hlog halpha
    have hLn : 0 ≤ Scale.L n :=
      Real.log_nonneg (by exact_mod_cast (Nat.le_of_lt hn))
    have hcensus : 0 ≤
        PaperGuardCensus.censusRatioMajorant Cprom Cbank n := by
      unfold PaperGuardCensus.censusRatioMajorant
      have hcoef : 0 ≤ (Cprom : ℝ) +
          3 * (Cbank : ℝ) * (Scale.L n + 2) := by positivity
      exact div_nonneg
        (mul_nonneg hcoef (Scale.y_pos (by omega : 0 < n)).le)
        (by positivity)
    have hmajor : 0 ≤
        guardPowerCorrectionWeightedMajorant Cprom Cbank Cenv D n := by
      unfold guardPowerCorrectionWeightedMajorant
      exact mul_nonneg (by positivity)
        (PaperGuardCensus.guardPowerCorrectionRowError_nonneg
          (mul_nonneg hCenv hLn) (mul_nonneg hD hcensus))
    have hdenom : 0 < c / Real.log (Scale.L n) := div_pos hc hlog
    calc
      guardPowerCorrectionWeightedMajorant Cprom Cbank Cenv D n /
          alpha₀ n ≤
        guardPowerCorrectionWeightedMajorant Cprom Cbank Cenv D n /
          (c / Real.log (Scale.L n)) :=
        div_le_div_of_nonneg_left hmajor hdenom halpha
      _ = (guardPowerCorrectionWeightedMajorant Cprom Cbank Cenv D n *
          Real.log (Scale.L n)) / c := by
        field_simp [hc.ne', hlog.ne']

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
