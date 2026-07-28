import Erdos390.Full.PaperGuardedStructuredSample
import Erdos390.Full.PaperStatisticNorm

/-!
# Prime-row perturbations from the concrete guard deletion

The central estimate is family-summed.  Thus the row cost is controlled by
the total valuation of one integer, `O(log n / log W)`, rather than by the
number of primes in the moving band.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperGuardCensus

open ArithmeticModel Scale StructuredCells HeadPattern
open FiniteProbability GuardedUniformCell
open ValuationTiltCell ArithmeticBandGeometry
open PaperScaleMarkedCell

noncomputable section

variable {Alpha I : Type*} [DecidableEq Alpha] [Fintype I]

/-- Family-summed version of the literal tilted-uniform guard-deletion
estimate. -/
theorem exists_deleteGuards_familyCovariance_bound
    (S G : Finset Alpha) (hS : S.Nonempty)
    (score : S → ℝ) (K : ℝ) (hscore : ∀ x, |score x| ≤ K)
    (F : S → ℝ) (H : I → S → ℝ) (KF KH : ℝ)
    (hKF : 0 ≤ KF) (hF : ∀ x, |F x| ≤ KF)
    (hH : ∀ x, ∑ i, |H i x| ≤ KH)
    (hsmallCensus :
      Real.exp (2 * K) * (G.card : ℝ) / (S.card : ℝ) ≤ (1 : ℝ) / 2) :
    ∃ hsmall :
        ((uniformOnFinset S hS).exponentialTilt score).guardMass
          (guardSubtype S G) < 1,
      ∑ i,
          |(((uniformOnFinset S hS).exponentialTilt score).deleteGuards
              (guardSubtype S G) hsmall).covariance F (H i) -
            ((uniformOnFinset S hS).exponentialTilt score).covariance F (H i)| ≤
        12 * KF * KH *
          (Real.exp (2 * K) * (G.card : ℝ) / (S.card : ℝ)) := by
  let mu := (uniformOnFinset S hS).exponentialTilt score
  let guards := guardSubtype S G
  let delta := Real.exp (2 * K) * (G.card : ℝ) / (S.card : ℝ)
  have hmass : mu.guardMass guards ≤ delta := by
    simpa only [mu, guards, delta] using
      tilted_uniform_guardMass_le S G hS score K hscore
  have hhalf : mu.guardMass guards ≤ (1 : ℝ) / 2 :=
    hmass.trans hsmallCensus
  have hsmall : mu.guardMass guards < 1 := by linarith
  refine ⟨hsmall, ?_⟩
  have hperturb := mu.guardPerturbation_le_four_mul_guardMass guards hhalf
  have hrow := mu.sum_abs_deleteGuards_covariance_sub_le
    guards hsmall F H hKF hF hH
  have hcoef : 0 ≤ 3 * KF * KH := by
    have hKH : 0 ≤ KH := by
      obtain ⟨x, hxS⟩ := hS
      have hx := hH ⟨x, hxS⟩
      exact le_trans (Finset.sum_nonneg fun i hi ↦ abs_nonneg _) hx
    positivity
  calc
    ∑ i, |(mu.deleteGuards guards hsmall).covariance F (H i) -
        mu.covariance F (H i)| ≤
        3 * KF * KH * mu.guardPerturbation guards := hrow
    _ ≤ 3 * KF * KH * (4 * mu.guardMass guards) :=
      mul_le_mul_of_nonneg_left hperturb hcoef
    _ ≤ 3 * KF * KH * (4 * delta) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hmass (by norm_num)) hcoef
    _ = 12 * KF * KH * delta := by ring
    _ = 12 * KF * KH *
        (Real.exp (2 * K) * (G.card : ℝ) / (S.card : ℝ)) := rfl

/-- The concrete census-to-cell ratio, using the proved raw-cell density. -/
theorem guard_card_div_rawCell_le
    {Head : Type*} [Fintype Head]
    (P : Head → Pattern) (Iphys : PhysicalIntervals)
    {n Cprom Cbank : ℕ} (G : Ledger n Cprom Cbank)
    (c : PaperBridgeFit.Cell Head) (hn : 1 ≤ n)
    (hdensity :
      paperCellDensity (P c.1) (Iphys.lower c.2) (Iphys.upper c.2) *
          (n : ℝ) / 2 ≤ (rawCell P Iphys n c).card) :
    (G.guards.card : ℝ) / ((rawCell P Iphys n c).card : ℝ) ≤
      2 * censusRatioMajorant Cprom Cbank n /
        paperCellDensity (P c.1) (Iphys.lower c.2) (Iphys.upper c.2) := by
  let density :=
    paperCellDensity (P c.1) (Iphys.lower c.2) (Iphys.upper c.2)
  have hdensityPos : 0 < density :=
    paperCellDensity_pos (P c.1) (Iphys.lower_lt_upper c.2)
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hrawPos : 0 < ((rawCell P Iphys n c).card : ℝ) :=
    (div_pos (mul_pos hdensityPos hnR) (by norm_num)).trans_le hdensity
  have hguard := G.cast_card_guards_le hn
  have hyfloor : (yNat n : ℝ) ≤ y n :=
    Nat.floor_le (Scale.y_pos (by omega : 0 < n)).le
  have hcoef : 0 ≤
      (Cprom : ℝ) + 3 * (Cbank : ℝ) * (L n + 2) := by
    have hL : 0 ≤ L n := Real.log_nonneg (by exact_mod_cast hn)
    positivity
  have hguardY : (G.guards.card : ℝ) ≤
      ((Cprom : ℝ) + 3 * (Cbank : ℝ) * (L n + 2)) * y n :=
    hguard.trans (mul_le_mul_of_nonneg_left hyfloor hcoef)
  have hdivRaw :
      (G.guards.card : ℝ) / ((rawCell P Iphys n c).card : ℝ) ≤
        (G.guards.card : ℝ) / (density * (n : ℝ) / 2) := by
    exact div_le_div_of_nonneg_left (by positivity)
      (div_pos (mul_pos hdensityPos hnR) (by norm_num)) hdensity
  calc
    (G.guards.card : ℝ) / ((rawCell P Iphys n c).card : ℝ) ≤
        (G.guards.card : ℝ) / (density * (n : ℝ) / 2) := hdivRaw
    _ ≤ (((Cprom : ℝ) + 3 * (Cbank : ℝ) * (L n + 2)) * y n) /
          (density * (n : ℝ) / 2) :=
      div_le_div_of_nonneg_right hguardY
        (div_nonneg (mul_nonneg hdensityPos.le hnR.le) (by norm_num))
    _ = 2 * censusRatioMajorant Cprom Cbank n / density := by
      unfold censusRatioMajorant
      field_simp [hdensityPos.ne', hnR.ne']

/-- Uniform valuation envelope on a literal raw physical cell. -/
theorem rawCell_totalBandValuation_le
    {Head : Type*} [Fintype Head]
    (P : Head → Pattern) (Iphys : PhysicalIntervals)
    {n W : ℕ} (hW : 1 < W) (c : PaperBridgeFit.Cell Head)
    (m : rawCell P Iphys n c) :
    (∑ q : BandPrime n W, valuation q.1 (m : ℕ)) ≤
      Real.log (physicalBound (Iphys.upper c.2) n : ℝ) /
        Real.log (W : ℝ) := by
  have hm : 0 < (m : ℕ) := by
    exact pos_of_mem_smoothInterval (mem_structuredCell.mp m.property).1
  have hmM : (m : ℕ) ≤ physicalBound (Iphys.upper c.2) n := by
    exact (mem_smoothInterval.mp (mem_structuredCell.mp m.property).1).2.1
  have hpW : ∀ q ∈ primeBand n W, W ≤ q := by
    intro q hq
    exact (cutoff_lt_of_mem_primeBand hq).le
  have hraw := sum_valuation_le_log_ratio (primeBand n W) hm hmM hW hpW
  calc
    (∑ q : BandPrime n W, valuation q.1 (m : ℕ)) =
        ∑ q ∈ (primeBand n W).attach, valuation q.1 (m : ℕ) := by
      rw [Finset.univ_eq_attach]
    _ = ∑ q ∈ primeBand n W, valuation q (m : ℕ) :=
      Finset.sum_attach (primeBand n W) (fun q ↦ valuation q (m : ℕ))
    _ ≤ _ := hraw

/-- The divisor-indicator family has the same total logarithmic envelope. -/
theorem rawCell_totalBandIndicator_le
    {Head : Type*} [Fintype Head]
    (P : Head → Pattern) (Iphys : PhysicalIntervals)
    {n W : ℕ} (hW : 1 < W) (c : PaperBridgeFit.Cell Head)
    (m : rawCell P Iphys n c) :
    (∑ q : BandPrime n W, |divInd q.1 (m : ℕ)|) ≤
      Real.log (physicalBound (Iphys.upper c.2) n : ℝ) /
        Real.log (W : ℝ) := by
  calc
    ∑ q : BandPrime n W, |divInd q.1 (m : ℕ)| ≤
        ∑ q : BandPrime n W, valuation q.1 (m : ℕ) := by
      apply Finset.sum_le_sum
      intro q hq
      have hm : 0 < (m : ℕ) := by
        exact pos_of_mem_smoothInterval (mem_structuredCell.mp m.property).1
      have hhigher := higherValuation_nonneg (prime_of_mem_primeBand q.2) hm
      rw [abs_of_nonneg (divInd_nonneg q.1 (m : ℕ))]
      unfold higherValuation at hhigher
      linarith
    _ ≤ _ := rawCell_totalBandValuation_le P Iphys hW c m

/-- A single medium-prime valuation is bounded by the total valuation
envelope. -/
theorem rawCell_valuation_le_total
    {Head : Type*} [Fintype Head]
    (P : Head → Pattern) (Iphys : PhysicalIntervals)
    {n W : ℕ} (p : BandPrime n W) (c : PaperBridgeFit.Cell Head)
    (m : rawCell P Iphys n c) :
    valuation p.1 (m : ℕ) ≤
      ∑ q : BandPrime n W, valuation q.1 (m : ℕ) := by
  exact Finset.single_le_sum (fun q hq ↦ valuation_nonneg q.1 (m : ℕ))
    (Finset.mem_univ p)

/-- The logarithmic envelope used in all concrete guard rows. -/
def valuationEnvelope
    {Head : Type*} [Fintype Head]
    (Iphys : PhysicalIntervals) (n W : ℕ)
    (c : PaperBridgeFit.Cell Head) : ℝ :=
  Real.log (physicalBound (Iphys.upper c.2) n : ℝ) / Real.log (W : ℝ)

/-- Literal squarefree covariance row after deleting the concrete ledger
guards from one tilted raw cell. -/
theorem exists_concrete_squarefree_guardRow
    {Head : Type*} [Fintype Head]
    (P : Head → Pattern) (Iphys : PhysicalIntervals)
    {n W Cprom Cbank : ℕ} (G : Ledger n Cprom Cbank)
    (c : PaperBridgeFit.Cell Head) (hW : 1 < W)
    (hS : (rawCell P Iphys n c).Nonempty)
    (score : rawCell P Iphys n c → ℝ) (K : ℝ)
    (hscore : ∀ m, |score m| ≤ K)
    (hsmallCensus : Real.exp (2 * K) * (G.guards.card : ℝ) /
      ((rawCell P Iphys n c).card : ℝ) ≤ (1 : ℝ) / 2)
    (p : BandPrime n W) :
    ∃ hsmall :
        ((uniformOnFinset (rawCell P Iphys n c) hS).exponentialTilt score).guardMass
          (guardSubtype (rawCell P Iphys n c) G.guards) < 1,
      ∑ q : BandPrime n W,
        |(((uniformOnFinset (rawCell P Iphys n c) hS).exponentialTilt score).deleteGuards
            (guardSubtype (rawCell P Iphys n c) G.guards)
              hsmall).covariance
            (fun m ↦ divInd p.1 (m : ℕ))
            (fun m ↦ divInd q.1 (m : ℕ)) -
          ((uniformOnFinset (rawCell P Iphys n c) hS).exponentialTilt score).covariance
            (fun m ↦ divInd p.1 (m : ℕ))
            (fun m ↦ divInd q.1 (m : ℕ))| ≤
        12 * valuationEnvelope Iphys n W c *
          (Real.exp (2 * K) * (G.guards.card : ℝ) /
            ((rawCell P Iphys n c).card : ℝ)) := by
  let S := rawCell P Iphys n c
  let F : S → ℝ := fun m ↦ divInd p.1 (m : ℕ)
  let H : BandPrime n W → S → ℝ :=
    fun q m ↦ divInd q.1 (m : ℕ)
  have hF : ∀ m, |F m| ≤ (1 : ℝ) := by
    intro m
    dsimp only [F]
    rw [abs_of_nonneg (divInd_nonneg p.1 (m : ℕ))]
    exact divInd_le_one p.1 (m : ℕ)
  have hH : ∀ m, ∑ q, |H q m| ≤ valuationEnvelope Iphys n W c := by
    intro m
    simpa only [H, S, valuationEnvelope] using
      rawCell_totalBandIndicator_le P Iphys hW c m
  have hrow := exists_deleteGuards_familyCovariance_bound
    (I := BandPrime n W) S G.guards hS score K hscore F H
      1 (valuationEnvelope Iphys n W c) (by norm_num) hF hH hsmallCensus
  simpa only [S, F, H, one_mul, mul_assoc] using hrow

/-- Literal full-valuation covariance row after deleting the same concrete
guards. -/
theorem exists_concrete_fullValuation_guardRow
    {Head : Type*} [Fintype Head]
    (P : Head → Pattern) (Iphys : PhysicalIntervals)
    {n W Cprom Cbank : ℕ} (G : Ledger n Cprom Cbank)
    (c : PaperBridgeFit.Cell Head) (hW : 1 < W)
    (hS : (rawCell P Iphys n c).Nonempty)
    (score : rawCell P Iphys n c → ℝ) (K : ℝ)
    (hscore : ∀ m, |score m| ≤ K)
    (hsmallCensus : Real.exp (2 * K) * (G.guards.card : ℝ) /
      ((rawCell P Iphys n c).card : ℝ) ≤ (1 : ℝ) / 2)
    (p : BandPrime n W) :
    ∃ hsmall :
        ((uniformOnFinset (rawCell P Iphys n c) hS).exponentialTilt score).guardMass
          (guardSubtype (rawCell P Iphys n c) G.guards) < 1,
      ∑ q : BandPrime n W,
        |(((uniformOnFinset (rawCell P Iphys n c) hS).exponentialTilt score).deleteGuards
            (guardSubtype (rawCell P Iphys n c) G.guards)
              hsmall).covariance
            (fun m ↦ valuation p.1 (m : ℕ))
            (fun m ↦ valuation q.1 (m : ℕ)) -
          ((uniformOnFinset (rawCell P Iphys n c) hS).exponentialTilt score).covariance
            (fun m ↦ valuation p.1 (m : ℕ))
            (fun m ↦ valuation q.1 (m : ℕ))| ≤
        12 * valuationEnvelope Iphys n W c ^ 2 *
          (Real.exp (2 * K) * (G.guards.card : ℝ) /
            ((rawCell P Iphys n c).card : ℝ)) := by
  let S := rawCell P Iphys n c
  let F : S → ℝ := fun m ↦ valuation p.1 (m : ℕ)
  let H : BandPrime n W → S → ℝ :=
    fun q m ↦ valuation q.1 (m : ℕ)
  have htotal : ∀ m : S,
      ∑ q : BandPrime n W, valuation q.1 (m : ℕ) ≤
        valuationEnvelope Iphys n W c := by
    intro m
    simpa only [S, valuationEnvelope] using
      rawCell_totalBandValuation_le P Iphys hW c m
  have hF : ∀ m, |F m| ≤ valuationEnvelope Iphys n W c := by
    intro m
    rw [abs_of_nonneg (valuation_nonneg p.1 (m : ℕ))]
    exact (rawCell_valuation_le_total P Iphys p c m).trans (htotal m)
  have hH : ∀ m, ∑ q, |H q m| ≤ valuationEnvelope Iphys n W c := by
    intro m
    simpa only [H, abs_of_nonneg (valuation_nonneg _ _)] using htotal m
  have henv0 : 0 ≤ valuationEnvelope Iphys n W c := by
    obtain ⟨m, hm⟩ := hS
    let ms : S := ⟨m, hm⟩
    exact le_trans (Finset.sum_nonneg fun q hq ↦ valuation_nonneg q.1 (ms : ℕ))
      (htotal ms)
  have hrow := exists_deleteGuards_familyCovariance_bound
    (I := BandPrime n W) S G.guards hS score K hscore F H
      (valuationEnvelope Iphys n W c) (valuationEnvelope Iphys n W c)
      henv0 hF hH hsmallCensus
  rcases hrow with ⟨hsmall, hbound⟩
  refine ⟨hsmall, ?_⟩
  simpa only [S, F, H, pow_two, mul_assoc] using hbound

/-- Coefficient-weighted full-valuation row.  The cost is proportional to
the actual coefficient sup norm, which is the form used for the compensated
score. -/
theorem exists_concrete_coefficient_guardRow
    {Head : Type*} [Fintype Head]
    (P : Head → Pattern) (Iphys : PhysicalIntervals)
    {n W Cprom Cbank : ℕ} (G : Ledger n Cprom Cbank)
    (c : PaperBridgeFit.Cell Head) (hW : 1 < W)
    (hS : (rawCell P Iphys n c).Nonempty)
    (score : rawCell P Iphys n c → ℝ) (K : ℝ)
    (hscore : ∀ m, |score m| ≤ K)
    (hsmallCensus : Real.exp (2 * K) * (G.guards.card : ℝ) /
      ((rawCell P Iphys n c).card : ℝ) ≤ (1 : ℝ) / 2)
    (coeff : BandPrime n W → ℝ) (Ccoeff : ℝ) (hCcoeff : 0 ≤ Ccoeff)
    (hcoeff : ∀ q, |coeff q| ≤ Ccoeff)
    (p : BandPrime n W) :
    ∃ hsmall :
        ((uniformOnFinset (rawCell P Iphys n c) hS).exponentialTilt score).guardMass
          (guardSubtype (rawCell P Iphys n c) G.guards) < 1,
      |(((uniformOnFinset (rawCell P Iphys n c) hS).exponentialTilt score).deleteGuards
          (guardSubtype (rawCell P Iphys n c) G.guards)
            hsmall).covariance
          (fun m ↦ valuation p.1 (m : ℕ))
          (fun m ↦ ∑ q : BandPrime n W,
            coeff q * valuation q.1 (m : ℕ)) -
        ((uniformOnFinset (rawCell P Iphys n c) hS).exponentialTilt score).covariance
          (fun m ↦ valuation p.1 (m : ℕ))
          (fun m ↦ ∑ q : BandPrime n W,
            coeff q * valuation q.1 (m : ℕ))| ≤
        12 * valuationEnvelope Iphys n W c *
          (Ccoeff * valuationEnvelope Iphys n W c) *
          (Real.exp (2 * K) * (G.guards.card : ℝ) /
            ((rawCell P Iphys n c).card : ℝ)) := by
  let S := rawCell P Iphys n c
  let F : S → ℝ := fun m ↦ valuation p.1 (m : ℕ)
  let H : Unit → S → ℝ := fun _ m ↦
    ∑ q : BandPrime n W, coeff q * valuation q.1 (m : ℕ)
  have htotal : ∀ m : S,
      ∑ q : BandPrime n W, valuation q.1 (m : ℕ) ≤
        valuationEnvelope Iphys n W c := by
    intro m
    simpa only [S, valuationEnvelope] using
      rawCell_totalBandValuation_le P Iphys hW c m
  have hF : ∀ m, |F m| ≤ valuationEnvelope Iphys n W c := by
    intro m
    rw [abs_of_nonneg (valuation_nonneg p.1 (m : ℕ))]
    exact (rawCell_valuation_le_total P Iphys p c m).trans (htotal m)
  have hHpoint : ∀ m : S, |H () m| ≤
      Ccoeff * valuationEnvelope Iphys n W c := by
    intro m
    calc
      |H () m| ≤ ∑ q : BandPrime n W,
          |coeff q * valuation q.1 (m : ℕ)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ q : BandPrime n W,
          |coeff q| * valuation q.1 (m : ℕ) := by
        apply Finset.sum_congr rfl
        intro q hq
        rw [abs_mul, abs_of_nonneg (valuation_nonneg q.1 (m : ℕ))]
      _ ≤ ∑ q : BandPrime n W,
          Ccoeff * valuation q.1 (m : ℕ) := by
        apply Finset.sum_le_sum
        intro q hq
        exact mul_le_mul_of_nonneg_right (hcoeff q)
          (valuation_nonneg q.1 (m : ℕ))
      _ = Ccoeff * ∑ q : BandPrime n W,
          valuation q.1 (m : ℕ) := by rw [Finset.mul_sum]
      _ ≤ Ccoeff * valuationEnvelope Iphys n W c :=
        mul_le_mul_of_nonneg_left (htotal m) hCcoeff
  have hH : ∀ m, ∑ u : Unit, |H u m| ≤
      Ccoeff * valuationEnvelope Iphys n W c := by
    intro m
    simpa using hHpoint m
  have henv0 : 0 ≤ valuationEnvelope Iphys n W c := by
    obtain ⟨m, hm⟩ := hS
    let ms : S := ⟨m, hm⟩
    exact le_trans (Finset.sum_nonneg fun q hq ↦ valuation_nonneg q.1 (ms : ℕ))
      (htotal ms)
  have hrow := exists_deleteGuards_familyCovariance_bound
    (I := Unit) S G.guards hS score K hscore F H
      (valuationEnvelope Iphys n W c)
      (Ccoeff * valuationEnvelope Iphys n W c)
      henv0 hF hH hsmallCensus
  rcases hrow with ⟨hsmall, hbound⟩
  refine ⟨hsmall, ?_⟩
  simpa [S, F, H] using hbound

end

end Erdos390.Full.PaperGuardCensus
