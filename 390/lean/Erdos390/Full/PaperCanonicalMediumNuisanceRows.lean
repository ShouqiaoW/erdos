import Erdos390.Full.PaperMediumNuisanceInputReduction
import Erdos390.Full.PaperBridgeCanonicalGuardPowerCorrection

/-!
# Canonical raw-cell attachment for the medium nuisance rows

This file contains the dependent-type bookkeeping which identifies the
guard-deleted exponential tilt on a literal raw structured cell with the
`cellMediumLaw` carried by canonical `BridgeData`.  In particular, later
moving-prefix and prime-power estimates can be proved on the raw cell and
transported to the exact laws used by the nuisance Schur complement without
an unrecorded change of sample space.
-/

open scoped BigOperators

namespace Erdos390.Full

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open PaperGuardCensus GuardedUniformCell ValuationScoreDomination

namespace FiniteProbability

variable {Alpha : Type*}

/-- Equality of the underlying finite sets, together with pointwise equality
of the scores and statistics, gives literal equality of tilted expectations.
The formulation is useful when the equality changes a subtype. -/
theorem uniformOnFinset_exponentialTilt_expect_eq_of_finset_eq
    (S T : Finset Alpha) (hST : S = T)
    (hS : S.Nonempty) (hT : T.Nonempty)
    (scoreS : S → ℝ) (scoreT : T → ℝ)
    (hscore : ∀ (x : S) (y : T), (x : Alpha) = (y : Alpha) →
      scoreS x = scoreT y)
    (F : Alpha → ℝ) :
    ((uniformOnFinset S hS).exponentialTilt scoreS).expect
        (fun x ↦ F (x : Alpha)) =
      ((uniformOnFinset T hT).exponentialTilt scoreT).expect
        (fun x ↦ F (x : Alpha)) := by
  subst T
  have hscoreEq : scoreS = scoreT := by
    funext x
    exact hscore x x rfl
  subst scoreT
  have hproof : hS = hT := Subsingleton.elim _ _
  subst hT
  rfl

/-- Covariance analogue of
`uniformOnFinset_exponentialTilt_expect_eq_of_finset_eq`. -/
theorem uniformOnFinset_exponentialTilt_covariance_eq_of_finset_eq
    (S T : Finset Alpha) (hST : S = T)
    (hS : S.Nonempty) (hT : T.Nonempty)
    (scoreS : S → ℝ) (scoreT : T → ℝ)
    (hscore : ∀ (x : S) (y : T), (x : Alpha) = (y : Alpha) →
      scoreS x = scoreT y)
    (F H : Alpha → ℝ) :
    ((uniformOnFinset S hS).exponentialTilt scoreS).covariance
        (fun x ↦ F (x : Alpha)) (fun x ↦ H (x : Alpha)) =
      ((uniformOnFinset T hT).exponentialTilt scoreT).covariance
        (fun x ↦ F (x : Alpha)) (fun x ↦ H (x : Alpha)) := by
  subst T
  have hscoreEq : scoreS = scoreT := by
    funext x
    exact hscore x x rfl
  subst scoreT
  have hproof : hS = hT := Subsingleton.elim _ _
  subst hT
  rfl

end FiniteProbability

namespace PaperBridgeFit

open HeadPattern

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- Exact expectation reindexing from the raw tilted cell after deleting the
concrete guards to the canonical `cellMediumLaw`. -/
theorem raw_deleteGuards_expect_eq_cellMediumLaw
    [Nonempty Head]
    (P : Head → Pattern) (I : PhysicalIntervals)
    {Cprom Cbank : ℕ} (G : Ledger B.sampleData.n Cprom Cbank)
    (hsep : physicalBound (I.upper .minus) B.sampleData.n <
      physicalBound (I.lower .plus) B.sampleData.n)
    (hremaining : ∀ c : Cell Head,
      (rawCell P I B.sampleData.n c \ G.guards).Nonempty)
    (hcanonical : B.sampleData =
      canonicalSampleData (W := B.sampleData.W) P I G hsep hremaining)
    (xi : B.ParamSpace) (c : Cell Head)
    (hsmall :
      ((uniformOnFinset (rawCell P I B.sampleData.n c)
        ((hremaining c).mono Finset.sdiff_subset)).exponentialTilt
          (fun m ↦ valuationScore
            (primeBand B.sampleData.n B.sampleData.W)
            (B.effectiveNatCoefficient xi) B.L (m : ℕ))).guardMass
        (guardSubtype (rawCell P I B.sampleData.n c) G.guards) < 1)
    (F : ℕ → ℝ) :
    (((uniformOnFinset (rawCell P I B.sampleData.n c)
        ((hremaining c).mono Finset.sdiff_subset)).exponentialTilt
          (fun m ↦ valuationScore
            (primeBand B.sampleData.n B.sampleData.W)
            (B.effectiveNatCoefficient xi) B.L (m : ℕ))).deleteGuards
        (guardSubtype (rawCell P I B.sampleData.n c) G.guards) hsmall).expect
          (fun m ↦ F (m : ℕ)) =
      (B.cellMediumLaw xi c).expect (fun m ↦ F (m : ℕ)) := by
  let S := rawCell P I B.sampleData.n c
  let hS : S.Nonempty := (hremaining c).mono Finset.sdiff_subset
  let score : S → ℝ := fun m ↦ valuationScore
    (primeBand B.sampleData.n B.sampleData.W)
    (B.effectiveNatCoefficient xi) B.L (m : ℕ)
  have hreindex := deleteGuards_tilted_uniform_expect_remaining_eq
    S G.guards hS (hremaining c) score hsmall (fun m ↦ F (m : ℕ))
  have hcellEq : B.sampleData.cellFinset c = S \ G.guards := by
    calc
      B.sampleData.cellFinset c =
          (canonicalSampleData (W := B.sampleData.W)
            P I G hsep hremaining).cellFinset c :=
        congrArg (fun D : StructuredSampleData Head ↦ D.cellFinset c)
          hcanonical
      _ = S \ G.guards := by
        simpa only [S] using
          canonicalSampleData_cellFinset P I G hsep hremaining c
  have htilt :=
    uniformOnFinset_exponentialTilt_expect_eq_of_finset_eq
      (S \ G.guards) (B.sampleData.cellFinset c) hcellEq.symm
      (hremaining c) (B.sampleData.cell_nonempty c)
      (fun z ↦ score (remainingEmbedding S G.guards z))
      (sigmaCellScore (B.scaledMediumScore xi) c)
      (by
        intro x y hxy
        rw [B.sigmaCellScore_scaledMedium_eq_valuationScore xi c y]
        dsimp only [score]
        rw [remainingEmbedding_value, hxy]) F
  exact hreindex.trans htilt

/-- Exact covariance reindexing from the raw tilted cell after deleting the
concrete guards to the canonical `cellMediumLaw`. -/
theorem raw_deleteGuards_covariance_eq_cellMediumLaw
    [Nonempty Head]
    (P : Head → Pattern) (I : PhysicalIntervals)
    {Cprom Cbank : ℕ} (G : Ledger B.sampleData.n Cprom Cbank)
    (hsep : physicalBound (I.upper .minus) B.sampleData.n <
      physicalBound (I.lower .plus) B.sampleData.n)
    (hremaining : ∀ c : Cell Head,
      (rawCell P I B.sampleData.n c \ G.guards).Nonempty)
    (hcanonical : B.sampleData =
      canonicalSampleData (W := B.sampleData.W) P I G hsep hremaining)
    (xi : B.ParamSpace) (c : Cell Head)
    (hsmall :
      ((uniformOnFinset (rawCell P I B.sampleData.n c)
        ((hremaining c).mono Finset.sdiff_subset)).exponentialTilt
          (fun m ↦ valuationScore
            (primeBand B.sampleData.n B.sampleData.W)
            (B.effectiveNatCoefficient xi) B.L (m : ℕ))).guardMass
        (guardSubtype (rawCell P I B.sampleData.n c) G.guards) < 1)
    (F H : ℕ → ℝ) :
    (((uniformOnFinset (rawCell P I B.sampleData.n c)
        ((hremaining c).mono Finset.sdiff_subset)).exponentialTilt
          (fun m ↦ valuationScore
            (primeBand B.sampleData.n B.sampleData.W)
            (B.effectiveNatCoefficient xi) B.L (m : ℕ))).deleteGuards
        (guardSubtype (rawCell P I B.sampleData.n c) G.guards) hsmall).covariance
          (fun m ↦ F (m : ℕ)) (fun m ↦ H (m : ℕ)) =
      (B.cellMediumLaw xi c).covariance
        (fun m ↦ F (m : ℕ)) (fun m ↦ H (m : ℕ)) := by
  let S := rawCell P I B.sampleData.n c
  let hS : S.Nonempty := (hremaining c).mono Finset.sdiff_subset
  let score : S → ℝ := fun m ↦ valuationScore
    (primeBand B.sampleData.n B.sampleData.W)
    (B.effectiveNatCoefficient xi) B.L (m : ℕ)
  have hreindex := deleteGuards_tilted_uniform_covariance_remaining_eq
    S G.guards hS (hremaining c) score hsmall
      (fun m ↦ F (m : ℕ)) (fun m ↦ H (m : ℕ))
  have hcellEq : B.sampleData.cellFinset c = S \ G.guards := by
    calc
      B.sampleData.cellFinset c =
          (canonicalSampleData (W := B.sampleData.W)
            P I G hsep hremaining).cellFinset c :=
        congrArg (fun D : StructuredSampleData Head ↦ D.cellFinset c)
          hcanonical
      _ = S \ G.guards := by
        simpa only [S] using
          canonicalSampleData_cellFinset P I G hsep hremaining c
  have htilt :=
    uniformOnFinset_exponentialTilt_covariance_eq_of_finset_eq
      (S \ G.guards) (B.sampleData.cellFinset c) hcellEq.symm
      (hremaining c) (B.sampleData.cell_nonempty c)
      (fun z ↦ score (remainingEmbedding S G.guards z))
      (sigmaCellScore (B.scaledMediumScore xi) c)
      (by
        intro x y hxy
        rw [B.sigmaCellScore_scaledMedium_eq_valuationScore xi c y]
        dsimp only [score]
        rw [remainingEmbedding_value, hxy]) F H
  exact hreindex.trans htilt

/-- A raw tilted moving-prefix bound survives the canonical guard deletion
with the literal census error.  The conclusion is stated directly for
`cellMediumLaw`, so no subtype identification is left to downstream uses. -/
theorem cellMediumLaw_prefix_bound_of_raw_tilt
    [Nonempty Head]
    (P : Head → Pattern) (I : PhysicalIntervals)
    {Cprom Cbank : ℕ} (G : Ledger B.sampleData.n Cprom Cbank)
    (hsep : physicalBound (I.upper .minus) B.sampleData.n <
      physicalBound (I.lower .plus) B.sampleData.n)
    (hremaining : ∀ c : Cell Head,
      (rawCell P I B.sampleData.n c \ G.guards).Nonempty)
    (hcanonical : B.sampleData =
      canonicalSampleData (W := B.sampleData.W) P I G hsep hremaining)
    (xi : B.ParamSpace) (c : Cell Head) (p : ℕ)
    {Kscore KA E : ℝ}
    (hKA : 0 ≤ KA)
    (hscore : ∀ m : rawCell P I B.sampleData.n c,
      |valuationScore (primeBand B.sampleData.n B.sampleData.W)
        (B.effectiveNatCoefficient xi) B.L (m : ℕ)| ≤ Kscore)
    (hvaluation : ∀ m : rawCell P I B.sampleData.n c,
      |(valuation p (m : ℕ) : ℝ)| ≤ KA)
    (hsmallCensus :
      Real.exp (2 * Kscore) * (G.guards.card : ℝ) /
        ((rawCell P I B.sampleData.n c).card : ℝ) ≤ (1 : ℝ) / 2)
    (hprefix : ∀ k : ℕ,
      |((uniformOnFinset (rawCell P I B.sampleData.n c)
          ((hremaining c).mono Finset.sdiff_subset)).exponentialTilt
        (fun m ↦ valuationScore
          (primeBand B.sampleData.n B.sampleData.W)
          (B.effectiveNatCoefficient xi) B.L (m : ℕ))).covariance
          (fun m ↦ (valuation p (m : ℕ) : ℝ))
          (fun m ↦ if (m : ℕ) ≤ k then 1 else 0)| ≤ E) :
    ∀ k : ℕ,
      |(B.cellMediumLaw xi c).covariance
          (fun m ↦ (valuation p (m : ℕ) : ℝ))
          (fun m ↦ if (m : ℕ) ≤ k then 1 else 0)| ≤
        E + 12 * KA *
          (Real.exp (2 * Kscore) * (G.guards.card : ℝ) /
            ((rawCell P I B.sampleData.n c).card : ℝ)) := by
  let S := rawCell P I B.sampleData.n c
  let hS : S.Nonempty := (hremaining c).mono Finset.sdiff_subset
  let score : S → ℝ := fun m ↦ valuationScore
    (primeBand B.sampleData.n B.sampleData.W)
    (B.effectiveNatCoefficient xi) B.L (m : ℕ)
  let value : S → ℕ := fun m ↦ (m : ℕ)
  let V : S → ℝ := fun m ↦ (valuation p (m : ℕ) : ℝ)
  have hprefixCentered : ∀ k,
      |∑ j ∈ Finset.Icc 0 k,
        FiniteLogStieltjes.centeredFiberMass
          ((uniformOnFinset S hS).exponentialTilt score) value V j| ≤ E := by
    intro k
    rw [FiniteLogStieltjes.sum_centeredFiberMass_Icc_eq_covariance_prefixIndicator]
    simpa only [S, hS, score, value, V] using hprefix k
  obtain ⟨hsmall, hdeleted⟩ :=
    GuardedUniformCell.exists_deleteGuards_centeredPrefix_bound
      S G.guards hS score Kscore
      (by simpa only [S, score] using hscore)
      value V hKA (by simpa only [S, V] using hvaluation)
      (by simpa only [S] using hsmallCensus) hprefixCentered
  intro k
  have hdelCov := hdeleted k
  rw [FiniteLogStieltjes.sum_centeredFiberMass_Icc_eq_covariance_prefixIndicator]
    at hdelCov
  have hreindex := B.raw_deleteGuards_covariance_eq_cellMediumLaw
    P I G hsep hremaining hcanonical xi c hsmall
      (fun m ↦ (valuation p m : ℝ))
      (fun m ↦ if m ≤ k then 1 else 0)
  rw [hreindex] at hdelCov
  simpa only [S, hS, score, value, V] using hdelCov

/-- A raw tilted divisor profile survives canonical guard deletion with the
exact `4δ` conditional-expectation loss. -/
theorem cellMediumLaw_divInd_profile_of_raw_tilt
    [Nonempty Head]
    (P : Head → Pattern) (I : PhysicalIntervals)
    {Cprom Cbank : ℕ} (G : Ledger B.sampleData.n Cprom Cbank)
    (hsep : physicalBound (I.upper .minus) B.sampleData.n <
      physicalBound (I.lower .plus) B.sampleData.n)
    (hremaining : ∀ c : Cell Head,
      (rawCell P I B.sampleData.n c \ G.guards).Nonempty)
    (hcanonical : B.sampleData =
      canonicalSampleData (W := B.sampleData.W) P I G hsep hremaining)
    (xi : B.ParamSpace) (c : Cell Head) (D : ℕ) (main E : ℝ)
    {Kscore : ℝ}
    (hscore : ∀ m : rawCell P I B.sampleData.n c,
      |valuationScore (primeBand B.sampleData.n B.sampleData.W)
        (B.effectiveNatCoefficient xi) B.L (m : ℕ)| ≤ Kscore)
    (hsmallCensus :
      Real.exp (2 * Kscore) * (G.guards.card : ℝ) /
        ((rawCell P I B.sampleData.n c).card : ℝ) ≤ (1 : ℝ) / 2)
    (hraw :
      |((uniformOnFinset (rawCell P I B.sampleData.n c)
          ((hremaining c).mono Finset.sdiff_subset)).exponentialTilt
        (fun m ↦ valuationScore
          (primeBand B.sampleData.n B.sampleData.W)
          (B.effectiveNatCoefficient xi) B.L (m : ℕ))).expect
          (fun m ↦ divInd D (m : ℕ)) - main| ≤ E) :
    |(B.cellMediumLaw xi c).expect (fun m ↦ divInd D (m : ℕ)) - main| ≤
      E + 4 * (Real.exp (2 * Kscore) * (G.guards.card : ℝ) /
        ((rawCell P I B.sampleData.n c).card : ℝ)) := by
  let S := rawCell P I B.sampleData.n c
  let hS : S.Nonempty := (hremaining c).mono Finset.sdiff_subset
  let score : S → ℝ := fun m ↦ valuationScore
    (primeBand B.sampleData.n B.sampleData.W)
    (B.effectiveNatCoefficient xi) B.L (m : ℕ)
  obtain ⟨hsmall, hdiff⟩ :=
    GuardedUniformCell.exists_deleteGuards_expect_bound
      S G.guards hS score Kscore
      (by simpa only [S, score] using hscore)
      (fun m ↦ divInd D (m : ℕ)) (by norm_num : 0 ≤ (1 : ℝ))
      (by
        intro m
        rw [abs_of_nonneg (divInd_nonneg D (m : ℕ))]
        exact divInd_le_one D (m : ℕ))
      (by simpa only [S] using hsmallCensus)
  have hreindex := B.raw_deleteGuards_expect_eq_cellMediumLaw
    P I G hsep hremaining hcanonical xi c hsmall
      (fun m ↦ divInd D m)
  have htri :
      |(B.cellMediumLaw xi c).expect (fun m ↦ divInd D (m : ℕ)) - main| ≤
        |(B.cellMediumLaw xi c).expect (fun m ↦ divInd D (m : ℕ)) -
          ((uniformOnFinset S hS).exponentialTilt score).expect
            (fun m ↦ divInd D (m : ℕ))| +
        |((uniformOnFinset S hS).exponentialTilt score).expect
            (fun m ↦ divInd D (m : ℕ)) - main| := by
    have h := abs_add_le
      ((B.cellMediumLaw xi c).expect (fun m ↦ divInd D (m : ℕ)) -
        ((uniformOnFinset S hS).exponentialTilt score).expect
          (fun m ↦ divInd D (m : ℕ)))
      (((uniformOnFinset S hS).exponentialTilt score).expect
        (fun m ↦ divInd D (m : ℕ)) - main)
    simpa only [sub_add_sub_cancel] using h
  calc
    |(B.cellMediumLaw xi c).expect (fun m ↦ divInd D (m : ℕ)) - main| ≤
        |(B.cellMediumLaw xi c).expect (fun m ↦ divInd D (m : ℕ)) -
          ((uniformOnFinset S hS).exponentialTilt score).expect
            (fun m ↦ divInd D (m : ℕ))| +
        |((uniformOnFinset S hS).exponentialTilt score).expect
            (fun m ↦ divInd D (m : ℕ)) - main| := htri
    _ = |((((uniformOnFinset S hS).exponentialTilt score).deleteGuards
          (guardSubtype S G.guards) hsmall).expect
            (fun m ↦ divInd D (m : ℕ))) -
          ((uniformOnFinset S hS).exponentialTilt score).expect
            (fun m ↦ divInd D (m : ℕ))| +
        |((uniformOnFinset S hS).exponentialTilt score).expect
            (fun m ↦ divInd D (m : ℕ)) - main| := by
      rw [hreindex]
    _ ≤ 4 * (Real.exp (2 * Kscore) * (G.guards.card : ℝ) /
          ((rawCell P I B.sampleData.n c).card : ℝ)) + E := by
      have hdiff' := hdiff
      norm_num at hdiff'
      exact add_le_add (by simpa only [S, hS, score] using hdiff')
        (by simpa only [S, hS, score] using hraw)
    _ = E + 4 * (Real.exp (2 * Kscore) * (G.guards.card : ℝ) /
          ((rawCell P I B.sampleData.n c).card : ℝ)) := by ring

/-- The exact finite terminal reduction for the two analytic nuisance inputs.
A moving-prefix row gives the physical covariance by finite Stieltjes
summation, while a common truncated prime-power profile plus a reciprocal
tail gives pairwise agreement of the component valuation means. -/
theorem medium_physical_and_pair_profiles_of_prefix_power_tail
    [Nonempty Head]
    (xi : B.ParamSpace)
    (Kcut : BandPrime B.sampleData.n B.sampleData.W → ℕ)
    (main : BandPrime B.sampleData.n B.sampleData.W → ℕ → ℝ)
    {Cprefix Cpower Ctail Kspan Lscale : ℝ}
    (hCprefix : 0 ≤ Cprefix) (hCpower : 0 ≤ Cpower)
    (hLscale : 0 < Lscale)
    (hlo : ∀ c : Cell Head, 0 < B.sampleData.lo c.2)
    (hspan : ∀ c : Cell Head,
      ((B.sampleData.hi c.2 : ℝ) - (B.sampleData.lo c.2 : ℝ)) /
          (B.sampleData.lo c.2 : ℝ) ≤ Kspan)
    (hprefix : ∀ (p : BandPrime B.sampleData.n B.sampleData.W)
      (c : Cell Head) (k : ℕ),
      |(B.cellMediumLaw xi c).covariance
          (fun m ↦ (valuation p.1 (m : ℕ) : ℝ))
          (fun m ↦ if (m : ℕ) ≤ k then 1 else 0)| ≤
        (Cprefix / Lscale) * (1 / (p.1 : ℝ)))
    (hprofile : ∀ (p : BandPrime B.sampleData.n B.sampleData.W)
      (c : Cell Head) (k : ℕ),
      k ∈ positiveExponents (Kcut p) →
      |(B.cellMediumLaw xi c).expect
          (fun m ↦ divInd (p.1 ^ k) (m : ℕ)) - main p k| ≤
        (Cpower / Lscale) * (1 / ((p.1 ^ k : ℕ) : ℝ)))
    (htail : ∀ (p : BandPrime B.sampleData.n B.sampleData.W)
      (c : Cell Head),
      |(B.cellMediumLaw xi c).expect (fun m ↦
          valuation p.1 (m : ℕ) -
            ∑ k ∈ positiveExponents (Kcut p),
              divInd (p.1 ^ k) (m : ℕ))| ≤
        (Ctail / Lscale) * (1 / (p.1 : ℝ))) :
    (∀ (p : BandPrime B.sampleData.n B.sampleData.W) (c : Cell Head),
      |(B.cellMediumLaw xi c).covariance
          (fun m ↦ valuation p.1 (m : ℕ))
          (fun m ↦ B.physicalScore ⟨c, m⟩)| ≤
        ((Kspan * Cprefix) / Lscale) * (1 / (p.1 : ℝ))) ∧
    (∀ (p : BandPrime B.sampleData.n B.sampleData.W)
      (c c' : Cell Head),
      |(B.cellMediumLaw xi c).expect
          (fun m ↦ valuation p.1 (m : ℕ)) -
        (B.cellMediumLaw xi c').expect
          (fun m ↦ valuation p.1 (m : ℕ))| ≤
        ((4 * Cpower + 2 * Ctail) / Lscale) *
          (1 / (p.1 : ℝ))) := by
  constructor
  · intro p c
    apply B.abs_cellMediumLaw_covariance_valuation_physical_le_of_prefix_rate
      xi c (prime_of_mem_primeBand p.2).pos hCprefix hLscale (hlo c)
        (hspan c)
    intro t ht
    rw [FiniteLogStieltjes.sum_centeredFiberMass_Icc_eq_covariance_prefixIndicator]
    exact hprefix p c ⌊t⌋₊
  · intro p c c'
    exact B.abs_cellMediumLaw_expect_valuation_sub_other_of_reciprocal_profiles
      xi c c' (main p) (prime_of_mem_primeBand p.2) hCpower hLscale
      (fun d k hk ↦ hprofile p d k hk) (fun d ↦ htail p d)

end BridgeData

end PaperBridgeFit

end

end Erdos390.Full
