import Erdos390.Full.PaperActualFastMarkedRowProfiles
import Erdos390.Full.PaperActualFullBandIdentification
import Erdos390.Full.SquarefreeReferenceOperatorIdentification

/-!
# Ordinary raw-row transfer to the actual full band operator

The sharp transfer divides an output row by its band centre.  The fast
solve instead uses an ordinary raw coefficient, so the prime rows are first
averaged with their exact harmonic mass.  The factor `1/p` then cancels that
mass and no moving-centre loss occurs.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open PaperWeightedInverseExport
open PrimePowerSharpBandTransfer
open SquarefreeSharpBandTransfer
open SquarefreeCovarianceReference

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- Averaging a reciprocal prime-row estimate over one exact band removes
the output reciprocal weight. -/
private theorem abs_normalized_fiber_sum_le
    {E : ℝ} (i : Band)
    (f : BandPrime B.sampleData.n B.sampleData.W → ℝ)
    (hf : ∀ p, |f p| ≤ E * (1 / (p.1 : ℝ))) :
    |(1 / B.harmonicMass i) *
        ∑ p ∈ B.partition.data.fiber i, f p| ≤ E := by
  have hH : 0 < B.harmonicMass i := B.harmonicMass_pos i
  have hsum :
      |∑ p ∈ B.partition.data.fiber i, f p| ≤
        E * B.harmonicMass i := by
    calc
      |∑ p ∈ B.partition.data.fiber i, f p| ≤
          ∑ p ∈ B.partition.data.fiber i, |f p| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ p ∈ B.partition.data.fiber i,
          E * (1 / (p.1 : ℝ)) := by
        apply Finset.sum_le_sum
        intro p hp
        exact hf p
      _ = E * B.harmonicMass i := by
        rw [← Finset.mul_sum]
        rfl
  rw [abs_mul, abs_of_pos (one_div_pos.mpr hH)]
  calc
    (1 / B.harmonicMass i) *
        |∑ p ∈ B.partition.data.fiber i, f p| ≤
      (1 / B.harmonicMass i) * (E * B.harmonicMass i) :=
        mul_le_mul_of_nonneg_left hsum (one_div_nonneg.mpr hH.le)
    _ = E := by field_simp [hH.ne']

/-- The signed squarefree profile comparison in an ordinary raw band row.
The off-diagonal error pays the total harmonic mass, exactly as in the
paper's `epsilon(n) log L -> 0` estimate. -/
theorem squarefreeBandRow_sub_referenceBandRow_le_ordinary
    [Nonempty Head]
    (xi : B.ParamSpace) (q : B.RawBandGauge)
    {epsilonOff epsilonDiag epsilonSecond H : ℝ}
    (hepsilonOff : 0 ≤ epsilonOff)
    (hepsilonSecond : 0 ≤ epsilonSecond)
    (hW : 0 < B.sampleData.W)
    (hH : ∑ j : Band, B.harmonicMass j ≤ H)
    (hentry : ∀ p r,
      p ∈ primeBand B.sampleData.n B.sampleData.W →
      r ∈ primeBand B.sampleData.n B.sampleData.W →
      |(B.actualValuationLaw xi).covII p r -
          squarefreeReferenceEntry B.sampleData.n p r| ≤
        epsilonOff * (1 / (p : ℝ)) * (1 / (r : ℝ)) +
          if p = r then
            epsilonDiag * (1 / (p : ℝ)) +
              epsilonSecond * (1 / (p : ℝ)) ^ 2
          else 0)
    (i : Band) :
    |squarefreeBandRow (B.actualValuationLaw xi) B.partition q.1 i -
        referenceBandRow B.partition q.1 i| ≤
      ‖q‖ * (epsilonOff * H + epsilonDiag +
        epsilonSecond * (1 / (B.sampleData.W : ℝ))) := by
  let E : ℝ := ‖q‖ * (epsilonOff * H + epsilonDiag +
    epsilonSecond * (1 / (B.sampleData.W : ℝ)))
  let f : BandPrime B.sampleData.n B.sampleData.W → ℝ := fun p ↦
    (∑ r : BandPrime B.sampleData.n B.sampleData.W,
        q.1 (B.partition.band r) *
          (B.actualValuationLaw xi).covII p.1 r.1) -
      ∑ r : BandPrime B.sampleData.n B.sampleData.W,
        q.1 (B.partition.band r) *
          squarefreeReferenceEntry B.sampleData.n p.1 r.1
  have hf (p : BandPrime B.sampleData.n B.sampleData.W) :
      |f p| ≤ E * (1 / (p.1 : ℝ)) := by
    have hp := B.bandSquarefreeRegression_sub_reference_marked_le
      xi q hepsilonOff hH hentry p.2
    rw [(B.bandRegression_markedRows_eq_sums xi q p.1).2] at hp
    have hpPos : (0 : ℝ) < p.1 := by
      exact_mod_cast (prime_of_mem_primeBand p.2).pos
    have hWR : (0 : ℝ) < B.sampleData.W := by exact_mod_cast hW
    have hWp : (B.sampleData.W : ℝ) ≤ p.1 := by
      exact_mod_cast (cutoff_lt_of_mem_primeBand p.2).le
    have hinv : 1 / (p.1 : ℝ) ≤ 1 / (B.sampleData.W : ℝ) :=
      one_div_le_one_div_of_le hWR hWp
    have hcoef :
        epsilonOff * H + epsilonDiag +
            epsilonSecond * (1 / (p.1 : ℝ)) ≤
          epsilonOff * H + epsilonDiag +
            epsilonSecond * (1 / (B.sampleData.W : ℝ)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hinv hepsilonSecond)
    have hscaled :
        ‖q‖ * (epsilonOff * H + epsilonDiag +
              epsilonSecond * (1 / (p.1 : ℝ))) * (1 / (p.1 : ℝ)) ≤
          E * (1 / (p.1 : ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ (one_div_nonneg.mpr hpPos.le)
      exact mul_le_mul_of_nonneg_left hcoef (norm_nonneg q)
    exact hp.trans (by simpa only [E] using hscaled)
  have havg := B.abs_normalized_fiber_sum_le i f hf
  unfold squarefreeBandRow referenceBandRow
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  simpa only [f, E] using havg

/-- Lemma 7.5's weighted full-versus-squarefree row also transfers to an
ordinary raw band coefficient without a least-centre divisor. -/
theorem fullBandRow_sub_squarefreeBandRow_le_ordinary
    [Nonempty Head]
    (xi : B.ParamSpace) (q : B.RawBandGauge) {R : ℝ}
    (hrow : ∀ r : BandPrime B.sampleData.n B.sampleData.W,
      (r.1 : ℝ) *
        ∑ s : BandPrime B.sampleData.n B.sampleData.W,
          |(B.actualValuationLaw xi).covVV r.1 s.1 -
            (B.actualValuationLaw xi).covII r.1 s.1| ≤ R)
    (i : Band) :
    |fullBandRow (B.actualValuationLaw xi) B.partition q.1 i -
        squarefreeBandRow (B.actualValuationLaw xi) B.partition q.1 i| ≤
      ‖q‖ * R := by
  let E : ℝ := ‖q‖ * R
  let f : BandPrime B.sampleData.n B.sampleData.W → ℝ := fun p ↦
    (∑ r : BandPrime B.sampleData.n B.sampleData.W,
        q.1 (B.partition.band r) *
          (B.actualValuationLaw xi).covVV p.1 r.1) -
      ∑ r : BandPrime B.sampleData.n B.sampleData.W,
        q.1 (B.partition.band r) *
          (B.actualValuationLaw xi).covII p.1 r.1
  have hf (p : BandPrime B.sampleData.n B.sampleData.W) :
      |f p| ≤ E * (1 / (p.1 : ℝ)) := by
    have hp := B.bandRegression_full_sub_squarefree_marked_le_of_weightedRow
      xi q hrow p.2
    rw [(B.bandRegression_markedRows_eq_sums xi q p.1).1,
      (B.bandRegression_markedRows_eq_sums xi q p.1).2] at hp
    simpa only [f, E] using hp
  have havg := B.abs_normalized_fiber_sum_le i f hf
  unfold fullBandRow squarefreeBandRow
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  simpa only [f, E] using havg

/-- Triangle from the literal actual full row to the signed Dickman
reference row in the ordinary raw norm. -/
theorem fullBandRow_sub_referenceBandRow_le_ordinary
    [Nonempty Head]
    (xi : B.ParamSpace) (q : B.RawBandGauge)
    {Esquare R : ℝ}
    (hsquare : ∀ i : Band,
      |squarefreeBandRow (B.actualValuationLaw xi) B.partition q.1 i -
        referenceBandRow B.partition q.1 i| ≤ ‖q‖ * Esquare)
    (hfull : ∀ i : Band,
      |fullBandRow (B.actualValuationLaw xi) B.partition q.1 i -
        squarefreeBandRow (B.actualValuationLaw xi) B.partition q.1 i| ≤
          ‖q‖ * R)
    (i : Band) :
    |fullBandRow (B.actualValuationLaw xi) B.partition q.1 i -
        referenceBandRow B.partition q.1 i| ≤
      ‖q‖ * (R + Esquare) := by
  calc
    |fullBandRow (B.actualValuationLaw xi) B.partition q.1 i -
        referenceBandRow B.partition q.1 i| ≤
      |fullBandRow (B.actualValuationLaw xi) B.partition q.1 i -
        squarefreeBandRow (B.actualValuationLaw xi) B.partition q.1 i| +
      |squarefreeBandRow (B.actualValuationLaw xi) B.partition q.1 i -
        referenceBandRow B.partition q.1 i| := by
      have := abs_add_le
        (fullBandRow (B.actualValuationLaw xi) B.partition q.1 i -
          squarefreeBandRow (B.actualValuationLaw xi) B.partition q.1 i)
        (squarefreeBandRow (B.actualValuationLaw xi) B.partition q.1 i -
          referenceBandRow B.partition q.1 i)
      simpa only [sub_add_sub_cancel] using this
    _ ≤ ‖q‖ * R + ‖q‖ * Esquare := add_le_add (hfull i) (hsquare i)
    _ = ‖q‖ * (R + Esquare) := by ring

end BridgeData
end
end Erdos390.Full.PaperBridgeFit
