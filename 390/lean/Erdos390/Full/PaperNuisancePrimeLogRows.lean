import Erdos390.Full.PaperActualTwoStageRegression
import Erdos390.Full.PaperBridgeCellTiltDecomposition
import Erdos390.Full.FiniteProbabilityCellConstantCovariance
import Erdos390.Full.PrimePowerCutoffCovariance

/-!
# Exact logarithmic decomposition of the nuisance rows

The physical nuisance coordinate is not an unrelated marked statistic.  The
finite factorization identity in `BridgeData.HasPrimeLogCompatibility`
expresses the medium-prime logarithmic score as a nonzero multiple of the
physical logarithm plus a function of the fixed head tag.  This file solves
that identity for the physical score and does so inside an arbitrary nuisance
linear functional.

The resulting covariance-row identity is exact at finite `n`.  It is the
algebraic attachment used in Lemma 8.6 before applying the analytic estimates
for the prime-log null row and for cell-constant head rows.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

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

/-- The cell-constant head function carried by a nuisance vector after its
physical coordinate has been removed. -/
def nuisanceHeadFunction [Nonempty Head]
    (z : B.NuisanceSpace) (h₀ : Head) : ℝ :=
  ∑ h : B.HeadIndex,
    z (NuisanceCoord.head h) *
      ((if h₀ = h.1 then 1 else 0) - B.headBaselineMass h.1)

/-- An arbitrary nuisance linear functional is exactly its physical
coefficient times `R`, plus a function of the tagged head pattern. -/
theorem inner_nuisanceStatistic_eq_physical_add_headFunction
    [Nonempty Head]
    (z : B.NuisanceSpace) (m : B.sampleData.Sample) :
    inner ℝ z (B.nuisanceStatistic m) =
      z NuisanceCoord.physical * B.physicalScore m +
        B.headFunctionScore (B.nuisanceHeadFunction z) m := by
  rw [PiLp.inner_apply, sum_nuisanceCoord]
  simp only [B.nuisanceStatistic_physical, B.nuisanceStatistic_head,
    RCLike.inner_apply, conj_trivial]
  unfold nuisanceHeadFunction headFunctionScore centeredHeadScore headIndicator
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro h hh
    ring

/-- The head function left after using
`primeLogScore = a * physicalScore + headFunctionScore phi` to eliminate the
physical score from a nuisance linear functional. -/
def primeLogRemainderHeadFunction [Nonempty Head]
    (z : B.NuisanceSpace) (a : ℝ) (phi : Head → ℝ) (h₀ : Head) : ℝ :=
  B.nuisanceHeadFunction z h₀ -
    (z NuisanceCoord.physical / a) * phi h₀

/-- Pointwise exact compatibility decomposition.  The only hypothesis is the
literal finite factorization identity and the nonvanishing of its physical
coefficient. -/
theorem inner_nuisanceStatistic_eq_primeLog_add_headFunction
    [Nonempty Head]
    (z : B.NuisanceSpace) {a : ℝ} {phi : Head → ℝ}
    (ha : a ≠ 0)
    (hcompat : ∀ m : B.sampleData.Sample,
      B.primeLogScore m =
        a * B.physicalScore m + B.headFunctionScore phi m)
    (m : B.sampleData.Sample) :
    inner ℝ z (B.nuisanceStatistic m) =
      (z NuisanceCoord.physical / a) * B.primeLogScore m +
        B.headFunctionScore
          (B.primeLogRemainderHeadFunction z a phi) m := by
  rw [B.inner_nuisanceStatistic_eq_physical_add_headFunction z m,
    hcompat m]
  unfold primeLogRemainderHeadFunction headFunctionScore
  field_simp [ha]
  ring

/-- Exact normalized covariance-row decomposition.  Thus the nuisance
cross-row estimate reduces, without any loss or limiting argument, to the
prime-log row and a cell-constant head row. -/
theorem normalizedBandCovarianceRow_inner_nuisance_eq
    [Nonempty Head]
    (xi : B.ParamSpace) (z : B.NuisanceSpace)
    {a : ℝ} {phi : Head → ℝ}
    (ha : a ≠ 0)
    (hcompat : ∀ m : B.sampleData.Sample,
      B.primeLogScore m =
        a * B.physicalScore m + B.headFunctionScore phi m) :
    B.normalizedBandCovarianceRow xi
        (fun m ↦ inner ℝ z (B.nuisanceStatistic m)) =
      (z NuisanceCoord.physical / a) •
          B.normalizedBandCovarianceRow xi B.primeLogScore +
        B.normalizedBandCovarianceRow xi
          (B.headFunctionScore
            (B.primeLogRemainderHeadFunction z a phi)) := by
  have hpoint :
      (fun m ↦ inner ℝ z (B.nuisanceStatistic m)) =
        fun m ↦
          (z NuisanceCoord.physical / a) * B.primeLogScore m +
            B.headFunctionScore
              (B.primeLogRemainderHeadFunction z a phi) m := by
    funext m
    exact B.inner_nuisanceStatistic_eq_primeLog_add_headFunction
      z ha hcompat m
  rw [hpoint, B.normalizedBandCovarianceRow_add,
    B.normalizedBandCovarianceRow_smul]

/-- The explicit tagged-head term in the paper's finite logarithmic
factorization. -/
def exactPrimeLogHeadFunction (h : Head) : ℝ :=
  (Real.log (B.sampleData.n : ℝ) - B.headLogScore h) /
    Real.log (ArithmeticModel.y B.sampleData.n)

/-- The compatibility identity with its actual coefficient displayed.  This
avoids selecting an arbitrary witness of `HasPrimeLogCompatibility`. -/
theorem primeLogScore_eq_explicit_physical_add_head
    (hhead : ∀ h : Head, ∀ p : ℕ,
      p ∈ (B.sampleData.pattern h).primes ↔
        p.Prime ∧ p ≤ B.sampleData.W)
    (m : B.sampleData.Sample) :
    B.primeLogScore m =
      (1 / Real.log (ArithmeticModel.y B.sampleData.n)) *
          B.physicalScore m +
        B.headFunctionScore B.exactPrimeLogHeadFunction m := by
  let logY : ℝ := Real.log (ArithmeticModel.y B.sampleData.n)
  have hsplit := B.log_value_eq_headLogScore_add_bandFactorization hhead m
  have hband :
      (∑ p ∈ ArithmeticModel.primeBand
          B.sampleData.n B.sampleData.W,
        ((B.sampleData.value m).factorization p : ℝ) *
          Real.log (p : ℝ)) =
        Real.log (B.sampleData.value m : ℝ) -
          B.headLogScore (B.sampleData.cellOf m).1 := by
    linarith
  have hvalue : (B.sampleData.value m : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (B.sampleData.value_pos m))
  have hn : (B.sampleData.n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt B.n_gt_one))
  have hlogY : logY ≠ 0 := by
    exact ne_of_gt (by simpa [logY] using B.log_y_pos)
  rw [B.primeLogScore_eq_bandFactorization_div m, hband]
  unfold physicalScore headFunctionScore exactPrimeLogHeadFunction
  rw [Real.log_div hvalue hn]
  dsimp only [logY] at hlogY
  field_simp [hlogY]
  ring

/-- The exact nuisance row specialized to the paper's head-prime condition.
Its physical coefficient is `z_physical * log y`; no separate nonzero-witness
hypothesis is present. -/
theorem normalizedBandCovarianceRow_inner_nuisance_eq_exactHeadPrimes
    [Nonempty Head]
    (xi : B.ParamSpace) (z : B.NuisanceSpace)
    (hhead : ∀ h : Head, ∀ p : ℕ,
      p ∈ (B.sampleData.pattern h).primes ↔
        p.Prime ∧ p ≤ B.sampleData.W) :
    B.normalizedBandCovarianceRow xi
        (fun m ↦ inner ℝ z (B.nuisanceStatistic m)) =
      (z NuisanceCoord.physical *
          Real.log (ArithmeticModel.y B.sampleData.n)) •
          B.normalizedBandCovarianceRow xi B.primeLogScore +
        B.normalizedBandCovarianceRow xi
          (B.headFunctionScore
            (B.primeLogRemainderHeadFunction z
              (1 / Real.log (ArithmeticModel.y B.sampleData.n))
              B.exactPrimeLogHeadFunction)) := by
  let logY : ℝ := Real.log (ArithmeticModel.y B.sampleData.n)
  have hlogY : logY ≠ 0 := by
    exact ne_of_gt (by simpa [logY] using B.log_y_pos)
  have hrow := B.normalizedBandCovarianceRow_inner_nuisance_eq
    xi z (a := 1 / logY) (phi := B.exactPrimeLogHeadFunction)
    (one_div_ne_zero hlogY)
    (fun m ↦ by
      simpa only [logY] using
        B.primeLogScore_eq_explicit_physical_add_head hhead m)
  have hcoef : z NuisanceCoord.physical / (1 / logY) =
      z NuisanceCoord.physical * logY := by
    field_simp [hlogY]
  rw [hcoef] at hrow
  simpa only [logY] using hrow

/-- The preceding row identity from the packaged compatibility predicate. -/
theorem normalizedBandCovarianceRow_inner_nuisance_eq_of_compatibility
    [Nonempty Head]
    (xi : B.ParamSpace) (z : B.NuisanceSpace)
    (hcompat : B.HasPrimeLogCompatibility)
    (hnonzero : ∀ a phi,
      (∀ m : B.sampleData.Sample,
        B.primeLogScore m =
          a * B.physicalScore m + B.headFunctionScore phi m) → a ≠ 0) :
    ∃ a : ℝ, ∃ phi : Head → ℝ,
      B.normalizedBandCovarianceRow xi
          (fun m ↦ inner ℝ z (B.nuisanceStatistic m)) =
        (z NuisanceCoord.physical / a) •
            B.normalizedBandCovarianceRow xi B.primeLogScore +
          B.normalizedBandCovarianceRow xi
            (B.headFunctionScore
              (B.primeLogRemainderHeadFunction z a phi)) := by
  obtain ⟨a, phi, hpoint⟩ := hcompat
  exact ⟨a, phi,
    B.normalizedBandCovarianceRow_inner_nuisance_eq
      xi z (hnonzero a phi hpoint) hpoint⟩

/-- A componentwise common expectation profile gives a global covariance
bound against every bounded head function.  The globally tilted cell weights
are the exact partition-function-reweighted weights; no baseline-weight
replacement is made here. -/
theorem abs_tiltedLaw_covariance_headFunction_le_of_common_cell_expect
    [Nonempty Head]
    (xi : B.ParamSpace) (F : B.sampleData.Sample → ℝ)
    (phi : Head → ℝ) (main error K : ℝ)
    (herror : 0 ≤ error) (hK : 0 ≤ K)
    (hphi : ∀ h, |phi h| ≤ K)
    (hcell : ∀ c : Cell Head,
      |((B.guardedCellProbability c).exponentialTilt
          (FiniteProbability.sigmaCellScore
            (B.scaledBridgeScore xi) c)).expect
          (fun x ↦ F ⟨c, x⟩) - main| ≤ error) :
    |(B.tiltedLaw xi).covariance F (B.headFunctionScore phi)| ≤
      2 * K * error := by
  rw [B.tiltedLaw_eq_tiltedSigmaMixture xi]
  exact FiniteProbability.abs_sigmaMixture_covariance_tagFunction_le_of_common_expect
      (FiniteProbability.tiltedSigmaWeight
        B.baselineCellProbability B.guardedCellProbability
        (B.scaledBridgeScore xi))
      (fun c ↦ (B.guardedCellProbability c).exponentialTilt
        (FiniteProbability.sigmaCellScore (B.scaledBridgeScore xi) c))
      F (fun c ↦ phi c.1) main error K herror hK
      (fun c ↦ hphi c.1) hcell

/-- Exact total-covariance estimate for the actual globally tilted bridge
law.  A bound for every within-cell covariance is combined with pairwise
agreement of the first statistic's component means.  The second statistic
may vary inside a cell; only a pointwise bound is required.  Thus the
between-cell term is accounted for explicitly rather than silently replacing
the global covariance by an average of component covariances. -/
theorem abs_tiltedLaw_covariance_le_of_cell_covariance_and_pairwise_expect
    [Nonempty Head]
    (xi : B.ParamSpace)
    (F G : B.sampleData.Sample → ℝ)
    {covError meanError K : ℝ}
    (hmeanError : 0 ≤ meanError)
    (hK : 0 ≤ K)
    (hcellCov : ∀ c : Cell Head,
      |((B.guardedCellProbability c).exponentialTilt
          (FiniteProbability.sigmaCellScore
            (B.scaledBridgeScore xi) c)).covariance
          (fun x ↦ F ⟨c, x⟩) (fun x ↦ G ⟨c, x⟩)| ≤ covError)
    (hpair : ∀ c c' : Cell Head,
      |((B.guardedCellProbability c).exponentialTilt
          (FiniteProbability.sigmaCellScore
            (B.scaledBridgeScore xi) c)).expect
          (fun x ↦ F ⟨c, x⟩) -
        ((B.guardedCellProbability c').exponentialTilt
          (FiniteProbability.sigmaCellScore
            (B.scaledBridgeScore xi) c')).expect
          (fun x ↦ F ⟨c', x⟩)| ≤ meanError)
    (hG : ∀ m, |G m| ≤ K) :
    |(B.tiltedLaw xi).covariance F G| ≤
      covError + 2 * K * meanError := by
  let weight := FiniteProbability.tiltedSigmaWeight
    B.baselineCellProbability B.guardedCellProbability
      (B.scaledBridgeScore xi)
  let mu : ∀ c : Cell Head, FiniteProbability (B.sampleData.SampleAt c) :=
    fun c ↦ (B.guardedCellProbability c).exponentialTilt
      (FiniteProbability.sigmaCellScore (B.scaledBridgeScore xi) c)
  let H : Cell Head → ℝ := fun c ↦
    (mu c).expect (fun x ↦ G ⟨c, x⟩)
  let mix : FiniteProbability B.sampleData.Sample :=
    FiniteProbability.sigmaMixture weight mu
  let c₀ : Cell Head := (Classical.choice inferInstance, PhysicalSign.minus)
  let main : ℝ := (mu c₀).expect (fun x ↦ F ⟨c₀, x⟩)
  have hH : ∀ c, |H c| ≤ K := by
    intro c
    unfold H FiniteProbability.expect
    calc
      |∑ x, (mu c).mass x * G ⟨c, x⟩| ≤
          ∑ x, |(mu c).mass x * G ⟨c, x⟩| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ x, (mu c).mass x * |G ⟨c, x⟩| := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [abs_mul, abs_of_nonneg ((mu c).mass_nonneg x)]
      _ ≤ ∑ x, (mu c).mass x * K := by
        apply Finset.sum_le_sum
        intro x hx
        exact mul_le_mul_of_nonneg_left (hG ⟨c, x⟩) ((mu c).mass_nonneg x)
      _ = K := by rw [← Finset.sum_mul, (mu c).mass_sum, one_mul]
  have hcommon : ∀ c,
      |(mu c).expect (fun x ↦ F ⟨c, x⟩) - main| ≤ meanError := by
    intro c
    exact hpair c c₀
  have hbetween :
      |mix.covariance F (fun m ↦ H m.1)| ≤ 2 * K * meanError := by
    exact FiniteProbability.abs_sigmaMixture_covariance_tagFunction_le_of_common_expect
      weight mu F H main meanError K hmeanError hK hH hcommon
  have hwithin :
      |∑ c, weight.mass c *
        (mu c).covariance (fun x ↦ F ⟨c, x⟩) (fun x ↦ G ⟨c, x⟩)| ≤
        covError := by
    calc
      |∑ c, weight.mass c *
          (mu c).covariance (fun x ↦ F ⟨c, x⟩) (fun x ↦ G ⟨c, x⟩)| ≤
          ∑ c, |weight.mass c *
            (mu c).covariance (fun x ↦ F ⟨c, x⟩) (fun x ↦ G ⟨c, x⟩)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ c, weight.mass c * covError := by
        apply Finset.sum_le_sum
        intro c hc
        rw [abs_mul, abs_of_nonneg (weight.mass_nonneg c)]
        exact mul_le_mul_of_nonneg_left (hcellCov c) (weight.mass_nonneg c)
      _ = covError := by
        rw [← Finset.sum_mul, weight.mass_sum, one_mul]
  have hcomponent (c : Cell Head) :
      (mu c).expect (fun x ↦ F ⟨c, x⟩ * G ⟨c, x⟩) =
        (mu c).covariance (fun x ↦ F ⟨c, x⟩) (fun x ↦ G ⟨c, x⟩) +
          (mu c).expect (fun x ↦ F ⟨c, x⟩) * H c := by
    unfold FiniteProbability.covariance H
    ring
  have htagProduct (c : Cell Head) :
      (mu c).expect (fun x ↦ F ⟨c, x⟩ * H c) =
        H c * (mu c).expect (fun x ↦ F ⟨c, x⟩) := by
    have hfun : (fun x ↦ F ⟨c, x⟩ * H c) =
        fun x ↦ H c * F ⟨c, x⟩ := by
      funext x
      ring
    rw [hfun, (mu c).expect_smul]
  have htagExpect (c : Cell Head) :
      (mu c).expect (fun _ ↦ H c) = H c := by
    unfold FiniteProbability.expect
    rw [← Finset.sum_mul, (mu c).mass_sum, one_mul]
  have hHdef (c : Cell Head) :
      (mu c).expect (fun x ↦ G ⟨c, x⟩) = H c := by
    rfl
  have hcross :
      (∑ c, weight.mass c *
        ((mu c).expect (fun x ↦ F ⟨c, x⟩) * H c)) =
      ∑ c, weight.mass c *
        (H c * (mu c).expect (fun x ↦ F ⟨c, x⟩)) := by
    apply Finset.sum_congr rfl
    intro c hc
    ring
  have hdecomp :
      mix.covariance F G =
        (∑ c, weight.mass c *
          (mu c).covariance (fun x ↦ F ⟨c, x⟩) (fun x ↦ G ⟨c, x⟩)) +
          mix.covariance F (fun m ↦ H m.1) := by
    dsimp only [mix]
    unfold FiniteProbability.covariance
    simp_rw [FiniteProbability.sigmaMixture_expect]
    simp_rw [hcomponent, htagProduct, htagExpect, hHdef]
    simp only [add_sub_cancel_right]
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib]
    rw [hcross]
    ring
  have hmix : B.tiltedLaw xi = mix := by
    simpa only [mix, weight, mu] using B.tiltedLaw_eq_tiltedSigmaMixture xi
  rw [hmix, hdecomp]
  exact (abs_add_le _ _).trans (add_le_add hwithin hbetween)

/-- Exact finite summation from common prime-power profiles to a pairwise
full-valuation component profile.  The theorem keeps the truncated-power
errors and the two literal valuation tails separate; it is the algebraic
step behind the paper's summation over `p^k` and does not conceal an
infinite-series or component-mixture argument. -/
theorem abs_fullTiltCell_expect_valuation_sub_other_of_power_profiles
    [Nonempty Head]
    (xi : B.ParamSpace) (c c' : Cell Head)
    {p Kcut : ℕ} (main error : ℕ → ℝ) {tailError : ℝ}
    (hprofile : ∀ (d : Cell Head) k,
      k ∈ positiveExponents Kcut →
      |((B.guardedCellProbability d).exponentialTilt
          (FiniteProbability.sigmaCellScore
            (B.scaledBridgeScore xi) d)).expect
          (fun m ↦ divInd (p ^ k) (m : ℕ)) - main k| ≤ error k)
    (htail : ∀ d : Cell Head,
      |((B.guardedCellProbability d).exponentialTilt
          (FiniteProbability.sigmaCellScore
            (B.scaledBridgeScore xi) d)).expect
          (fun m ↦ valuation p (m : ℕ) -
            ∑ k ∈ positiveExponents Kcut, divInd (p ^ k) (m : ℕ))| ≤
        tailError) :
    |((B.guardedCellProbability c).exponentialTilt
          (FiniteProbability.sigmaCellScore
            (B.scaledBridgeScore xi) c)).expect
          (fun m ↦ valuation p (m : ℕ)) -
        ((B.guardedCellProbability c').exponentialTilt
          (FiniteProbability.sigmaCellScore
            (B.scaledBridgeScore xi) c')).expect
          (fun m ↦ valuation p (m : ℕ))| ≤
      2 * (∑ k ∈ positiveExponents Kcut, error k) + 2 * tailError := by
  let mu : ∀ d : Cell Head, FiniteProbability (B.sampleData.SampleAt d) :=
    fun d ↦ (B.guardedCellProbability d).exponentialTilt
      (FiniteProbability.sigmaCellScore (B.scaledBridgeScore xi) d)
  let trunc (d : Cell Head) : ℝ :=
    (mu d).expect (fun m ↦
      ∑ k ∈ positiveExponents Kcut, divInd (p ^ k) (m : ℕ))
  let tail (d : Cell Head) : ℝ :=
    (mu d).expect (fun m ↦ valuation p (m : ℕ) -
      ∑ k ∈ positiveExponents Kcut, divInd (p ^ k) (m : ℕ))
  have hexpect (d : Cell Head) :
      (mu d).expect (fun m ↦ valuation p (m : ℕ)) =
        trunc d + tail d := by
    have hpoint : (fun m : B.sampleData.SampleAt d ↦
        valuation p (m : ℕ)) =
      fun m : B.sampleData.SampleAt d ↦
        (∑ k ∈ positiveExponents Kcut, divInd (p ^ k) (m : ℕ)) +
          (valuation p (m : ℕ) -
            ∑ k ∈ positiveExponents Kcut, divInd (p ^ k) (m : ℕ)) := by
      funext m
      ring
    rw [hpoint, (mu d).expect_add]
  have htruncExpand (d : Cell Head) :
      trunc d = ∑ k ∈ positiveExponents Kcut,
        (mu d).expect (fun m ↦ divInd (p ^ k) (m : ℕ)) := by
    exact PrimePowerCutoffCovariance.FiniteProbability.expect_sum (mu d)
      (positiveExponents Kcut) (fun k m ↦ divInd (p ^ k) (m : ℕ))
  have hpower (k : ℕ) (hk : k ∈ positiveExponents Kcut) :
      |(mu c).expect (fun m ↦ divInd (p ^ k) (m : ℕ)) -
        (mu c').expect (fun m ↦ divInd (p ^ k) (m : ℕ))| ≤
        2 * error k := by
    have hc := hprofile c k hk
    have hc' := hprofile c' k hk
    calc
      |(mu c).expect (fun m ↦ divInd (p ^ k) (m : ℕ)) -
          (mu c').expect (fun m ↦ divInd (p ^ k) (m : ℕ))| ≤
        |(mu c).expect (fun m ↦ divInd (p ^ k) (m : ℕ)) - main k| +
          |(mu c').expect (fun m ↦ divInd (p ^ k) (m : ℕ)) - main k| := by
        have h := abs_add_le
          ((mu c).expect (fun m ↦ divInd (p ^ k) (m : ℕ)) - main k)
          (main k - (mu c').expect (fun m ↦ divInd (p ^ k) (m : ℕ)))
        simpa only [sub_add_sub_cancel, abs_sub_comm] using h
      _ ≤ error k + error k := add_le_add hc hc'
      _ = 2 * error k := by ring
  have htrunc :
      |trunc c - trunc c'| ≤
        2 * (∑ k ∈ positiveExponents Kcut, error k) := by
    rw [htruncExpand, htruncExpand, ← Finset.sum_sub_distrib]
    calc
      |∑ k ∈ positiveExponents Kcut,
          ((mu c).expect (fun m ↦ divInd (p ^ k) (m : ℕ)) -
            (mu c').expect (fun m ↦ divInd (p ^ k) (m : ℕ)))| ≤
        ∑ k ∈ positiveExponents Kcut,
          |(mu c).expect (fun m ↦ divInd (p ^ k) (m : ℕ)) -
            (mu c').expect (fun m ↦ divInd (p ^ k) (m : ℕ))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ positiveExponents Kcut, 2 * error k := by
        apply Finset.sum_le_sum
        intro k hk
        exact hpower k hk
      _ = 2 * (∑ k ∈ positiveExponents Kcut, error k) := by
        rw [Finset.mul_sum]
  have htailPair : |tail c - tail c'| ≤ 2 * tailError := by
    calc
      |tail c - tail c'| ≤ |tail c| + |tail c'| := abs_sub _ _
      _ ≤ tailError + tailError := add_le_add (htail c) (htail c')
      _ = 2 * tailError := by ring
  change |(mu c).expect (fun m ↦ valuation p (m : ℕ)) -
    (mu c').expect (fun m ↦ valuation p (m : ℕ))| ≤ _
  rw [hexpect, hexpect]
  calc
    |trunc c + tail c - (trunc c' + tail c')| =
        |(trunc c - trunc c') + (tail c - tail c')| := by ring_nf
    _ ≤ |trunc c - trunc c'| + |tail c - tail c'| := abs_add_le _ _
    _ ≤ 2 * (∑ k ∈ positiveExponents Kcut, error k) +
        2 * tailError := add_le_add htrunc htailPair

/-- The centered indicator of one retained head pattern, regarded as a
function of the full head tag.  Writing this function explicitly lets the
component-mixture cancellation be applied to the literal nuisance
coordinate, rather than to an unnamed bounded tag function. -/
def centeredHeadTagFunction [Nonempty Head]
    (h : B.HeadIndex) (h₀ : Head) : ℝ :=
  (if h₀ = h.1 then 1 else 0) - B.headBaselineMass h.1

theorem headFunctionScore_centeredHeadTagFunction
    [Nonempty Head] (h : B.HeadIndex) :
    B.headFunctionScore (B.centeredHeadTagFunction h) =
      B.centeredHeadScore h := by
  funext m
  unfold headFunctionScore centeredHeadTagFunction centeredHeadScore
    headIndicator
  rfl

theorem abs_centeredHeadTagFunction_le_three
    [Nonempty Head] (h : B.HeadIndex) (h₀ : Head) :
    |B.centeredHeadTagFunction h h₀| ≤ 3 := by
  have hbase0 : 0 ≤ B.headBaselineMass h.1 :=
    PaperStatisticNorm.BridgeData.headBaselineMass_nonneg B h.1
  have hbase2 : B.headBaselineMass h.1 ≤ 2 :=
    PaperStatisticNorm.BridgeData.headBaselineMass_le_two B h.1
  unfold centeredHeadTagFunction
  split_ifs
  all_goals rw [abs_le]
  all_goals constructor <;> linarith

/-- Pairwise agreement of the exact component means is enough for the
literal centered head coordinate.  A reference component supplies the
`main` in the common-profile mixture identity, so no limiting component
weights and no independently postulated head covariance row occur in the
statement. -/
theorem abs_tiltedLaw_covariance_nuisanceHead_le_of_pairwise_cell_expect
    [Nonempty Head]
    (xi : B.ParamSpace) (F : B.sampleData.Sample → ℝ)
    (h : B.HeadIndex) {error : ℝ} (herror : 0 ≤ error)
    (hpair : ∀ c c' : Cell Head,
      |((B.guardedCellProbability c).exponentialTilt
          (FiniteProbability.sigmaCellScore
            (B.scaledBridgeScore xi) c)).expect
          (fun x ↦ F ⟨c, x⟩) -
        ((B.guardedCellProbability c').exponentialTilt
          (FiniteProbability.sigmaCellScore
            (B.scaledBridgeScore xi) c')).expect
          (fun x ↦ F ⟨c', x⟩)| ≤ error) :
    |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m (NuisanceCoord.head h)) F| ≤
      6 * error := by
  let c₀ : Cell Head := (Classical.choice inferInstance, PhysicalSign.minus)
  let main : ℝ :=
    ((B.guardedCellProbability c₀).exponentialTilt
      (FiniteProbability.sigmaCellScore
        (B.scaledBridgeScore xi) c₀)).expect (fun x ↦ F ⟨c₀, x⟩)
  have hcommon : ∀ c : Cell Head,
      |((B.guardedCellProbability c).exponentialTilt
          (FiniteProbability.sigmaCellScore
            (B.scaledBridgeScore xi) c)).expect
          (fun x ↦ F ⟨c, x⟩) - main| ≤ error := by
    intro c
    exact hpair c c₀
  have hraw := B.abs_tiltedLaw_covariance_headFunction_le_of_common_cell_expect
    xi F (B.centeredHeadTagFunction h) main error 3 herror (by norm_num)
    (B.abs_centeredHeadTagFunction_le_three h) hcommon
  have hcoord :
      (fun m ↦ B.nuisanceStatistic m (NuisanceCoord.head h)) =
        B.centeredHeadScore h := by
    funext m
    exact B.nuisanceStatistic_head m h
  rw [(B.tiltedLaw xi).covariance_comm]
  rw [hcoord]
  rw [← B.headFunctionScore_centeredHeadTagFunction h]
  convert hraw using 1
  ring

/-- The paper's full nuisance marked family is a consequence of exactly two
analytic inputs: the physical marked row and pairwise agreement of the
component valuation means.  The head coordinates are discharged internally
by the preceding finite-mixture cancellation. -/
theorem abs_tiltedLaw_covariance_nuisanceCoord_le_of_pairwise_cell_expect
    [Nonempty Head]
    (xi : B.ParamSpace) (F : B.sampleData.Sample → ℝ)
    {error : ℝ} (herror : 0 ≤ error)
    (hphysical :
      |(B.tiltedLaw xi).covariance
          (fun m ↦ B.nuisanceStatistic m NuisanceCoord.physical) F| ≤
        6 * error)
    (hpair : ∀ c c' : Cell Head,
      |((B.guardedCellProbability c).exponentialTilt
          (FiniteProbability.sigmaCellScore
            (B.scaledBridgeScore xi) c)).expect
          (fun x ↦ F ⟨c, x⟩) -
        ((B.guardedCellProbability c').exponentialTilt
          (FiniteProbability.sigmaCellScore
            (B.scaledBridgeScore xi) c')).expect
          (fun x ↦ F ⟨c', x⟩)| ≤ error) :
    ∀ z : NuisanceCoord B.HeadIndex,
      |(B.tiltedLaw xi).covariance
          (fun m ↦ B.nuisanceStatistic m z) F| ≤ 6 * error := by
  intro z
  cases z with
  | physical => exact hphysical
  | head h =>
      exact B.abs_tiltedLaw_covariance_nuisanceHead_le_of_pairwise_cell_expect
        xi F h herror hpair

/-- Reciprocal-scale specialization for the actual medium-prime valuation
family.  This is the finite statement corresponding to the paper's
`O(1/(pL))` nuisance marked family: the physical Stieltjes row and the
pairwise exact-cell comparison are the only analytic hypotheses. -/
theorem nuisanceMarkedRows_le_of_pairwise_cell_valuation_and_physical
    [Nonempty Head]
    (xi : B.ParamSpace) {Cscale Lscale : ℝ}
    (hCscale : 0 ≤ Cscale) (hLscale : 0 < Lscale)
    (hphysical : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |(B.tiltedLaw xi).covariance
          (fun m ↦ B.nuisanceStatistic m NuisanceCoord.physical)
          (fun m ↦ valuation p.1 (B.sampleData.value m))| ≤
        (Cscale / Lscale) * (1 / (p.1 : ℝ)))
    (hpair : ∀ (p : BandPrime B.sampleData.n B.sampleData.W)
      (c c' : Cell Head),
      |((B.guardedCellProbability c).exponentialTilt
          (FiniteProbability.sigmaCellScore
            (B.scaledBridgeScore xi) c)).expect
          (fun x ↦ valuation p.1 (x : ℕ)) -
        ((B.guardedCellProbability c').exponentialTilt
          (FiniteProbability.sigmaCellScore
            (B.scaledBridgeScore xi) c')).expect
          (fun x ↦ valuation p.1 (x : ℕ))| ≤
        (Cscale / Lscale) * (1 / (p.1 : ℝ))) :
    ∀ (z : NuisanceCoord B.HeadIndex)
      (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw xi).covariance
          (fun m ↦ B.nuisanceStatistic m z)
          (fun m ↦ valuation p.1 (B.sampleData.value m))| ≤
        (6 * Cscale / Lscale) * (1 / (p.1 : ℝ)) := by
  intro z p
  let error : ℝ := (Cscale / Lscale) * (1 / (p.1 : ℝ))
  have hp : (0 : ℝ) < p.1 := by
    exact_mod_cast (prime_of_mem_primeBand p.2).pos
  have herror : 0 ≤ error :=
    mul_nonneg (div_nonneg hCscale hLscale.le) (one_div_nonneg.mpr hp.le)
  have hphysical' :
      |(B.tiltedLaw xi).covariance
          (fun m ↦ B.nuisanceStatistic m NuisanceCoord.physical)
          (fun m ↦ valuation p.1 (B.sampleData.value m))| ≤
        6 * error := by
    exact (hphysical p).trans (by nlinarith)
  have hrows := B.abs_tiltedLaw_covariance_nuisanceCoord_le_of_pairwise_cell_expect
    xi (fun m ↦ valuation p.1 (B.sampleData.value m)) herror hphysical'
    (fun c c' ↦ hpair p c c') z
  change |(B.tiltedLaw xi).covariance
      (fun m ↦ B.nuisanceStatistic m z)
      (fun m ↦ valuation p.1 (B.sampleData.value m))| ≤ _ at hrows
  calc
    |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m z)
        (fun m ↦ valuation p.1 (B.sampleData.value m))| ≤
        6 * error := hrows
    _ = (6 * Cscale / Lscale) * (1 / (p.1 : ℝ)) := by
      dsimp only [error]
      ring

/-- The global physical marked row is itself a consequence of the literal
within-cell Stieltjes covariance estimate and the same pairwise component
mean comparison used for the head rows.  This is the exact law-of-total-
covariance attachment: no global physical-row estimate is postulated. -/
theorem nuisanceMarkedRows_le_of_cell_physical_covariance_and_pairwise_valuation
    [Nonempty Head]
    (xi : B.ParamSpace) {Cscale Lscale K : ℝ}
    (hCscale : 0 ≤ Cscale) (hLscale : 0 < Lscale) (hK : 0 ≤ K)
    (hphysicalBound : ∀ m : B.sampleData.Sample,
      |B.physicalScore m| ≤ K)
    (hcellPhysical : ∀ (p : BandPrime B.sampleData.n B.sampleData.W)
      (c : Cell Head),
      |((B.guardedCellProbability c).exponentialTilt
          (FiniteProbability.sigmaCellScore
            (B.scaledBridgeScore xi) c)).covariance
          (fun x ↦ valuation p.1 (x : ℕ))
          (fun x ↦ B.physicalScore ⟨c, x⟩)| ≤
        (Cscale / Lscale) * (1 / (p.1 : ℝ)))
    (hpair : ∀ (p : BandPrime B.sampleData.n B.sampleData.W)
      (c c' : Cell Head),
      |((B.guardedCellProbability c).exponentialTilt
          (FiniteProbability.sigmaCellScore
            (B.scaledBridgeScore xi) c)).expect
          (fun x ↦ valuation p.1 (x : ℕ)) -
        ((B.guardedCellProbability c').exponentialTilt
          (FiniteProbability.sigmaCellScore
            (B.scaledBridgeScore xi) c')).expect
          (fun x ↦ valuation p.1 (x : ℕ))| ≤
        (Cscale / Lscale) * (1 / (p.1 : ℝ))) :
    ∀ (z : NuisanceCoord B.HeadIndex)
      (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw xi).covariance
          (fun m ↦ B.nuisanceStatistic m z)
          (fun m ↦ valuation p.1 (B.sampleData.value m))| ≤
        (6 * ((1 + 2 * K) * Cscale) / Lscale) *
          (1 / (p.1 : ℝ)) := by
  have hCfull : 0 ≤ (1 + 2 * K) * Cscale := by positivity
  have hphysical : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |(B.tiltedLaw xi).covariance
          (fun m ↦ B.nuisanceStatistic m NuisanceCoord.physical)
          (fun m ↦ valuation p.1 (B.sampleData.value m))| ≤
        (((1 + 2 * K) * Cscale) / Lscale) * (1 / (p.1 : ℝ)) := by
    intro p
    let error : ℝ := (Cscale / Lscale) * (1 / (p.1 : ℝ))
    have hp : (0 : ℝ) < p.1 := by
      exact_mod_cast (prime_of_mem_primeBand p.2).pos
    have herror : 0 ≤ error :=
      mul_nonneg (div_nonneg hCscale hLscale.le)
        (one_div_nonneg.mpr hp.le)
    have hraw :=
      B.abs_tiltedLaw_covariance_le_of_cell_covariance_and_pairwise_expect
        xi
        (fun m ↦ valuation p.1 (B.sampleData.value m))
        B.physicalScore herror hK
        (fun c ↦ hcellPhysical p c)
        (fun c c' ↦ hpair p c c') hphysicalBound
    have hcoord :
        (fun m ↦ B.nuisanceStatistic m NuisanceCoord.physical) =
          B.physicalScore := by
      funext m
      exact B.nuisanceStatistic_physical m
    rw [hcoord]
    calc
      |(B.tiltedLaw xi).covariance B.physicalScore
          (fun m ↦ valuation p.1 (B.sampleData.value m))| =
          |(B.tiltedLaw xi).covariance
            (fun m ↦ valuation p.1 (B.sampleData.value m))
            B.physicalScore| := by
        rw [(B.tiltedLaw xi).covariance_comm]
      _ ≤ error + 2 * K * error := hraw
      _ = (((1 + 2 * K) * Cscale) / Lscale) *
          (1 / (p.1 : ℝ)) := by
        dsimp only [error]
        ring
  have hpairFull : ∀ (p : BandPrime B.sampleData.n B.sampleData.W)
      (c c' : Cell Head),
      |((B.guardedCellProbability c).exponentialTilt
          (FiniteProbability.sigmaCellScore
            (B.scaledBridgeScore xi) c)).expect
          (fun x ↦ valuation p.1 (x : ℕ)) -
        ((B.guardedCellProbability c').exponentialTilt
          (FiniteProbability.sigmaCellScore
            (B.scaledBridgeScore xi) c')).expect
          (fun x ↦ valuation p.1 (x : ℕ))| ≤
        (((1 + 2 * K) * Cscale) / Lscale) *
          (1 / (p.1 : ℝ)) := by
    intro p c c'
    have hp : (0 : ℝ) < p.1 := by
      exact_mod_cast (prime_of_mem_primeBand p.2).pos
    have hsmall := hpair p c c'
    have hfactor : (1 : ℝ) ≤ 1 + 2 * K := by linarith
    have hbase : 0 ≤ (Cscale / Lscale) * (1 / (p.1 : ℝ)) :=
      mul_nonneg (div_nonneg hCscale hLscale.le)
        (one_div_nonneg.mpr hp.le)
    calc
      |((B.guardedCellProbability c).exponentialTilt
            (FiniteProbability.sigmaCellScore
              (B.scaledBridgeScore xi) c)).expect
            (fun x ↦ valuation p.1 (x : ℕ)) -
          ((B.guardedCellProbability c').exponentialTilt
            (FiniteProbability.sigmaCellScore
              (B.scaledBridgeScore xi) c')).expect
            (fun x ↦ valuation p.1 (x : ℕ))| ≤
          (Cscale / Lscale) * (1 / (p.1 : ℝ)) := hsmall
      _ ≤ (1 + 2 * K) *
          ((Cscale / Lscale) * (1 / (p.1 : ℝ))) :=
        (by
          simpa only [one_mul] using
            mul_le_mul_of_nonneg_right hfactor hbase)
      _ = (((1 + 2 * K) * Cscale) / Lscale) *
          (1 / (p.1 : ℝ)) := by ring
  exact B.nuisanceMarkedRows_le_of_pairwise_cell_valuation_and_physical
    xi hCfull hLscale hphysical hpairFull

/-- The pairwise exact-cell comparison therefore controls the *actual*
post-band nuisance covariance vector.  This is the precise finite summation
behind the paper's `O(w/L)` Schur-loss estimate; the vector estimate is not an
additional analytic premise. -/
theorem nuisanceCovarianceVector_postBand_norm_le_of_pairwise_cells
    [Nonempty Head]
    (xi : B.ParamSpace) (q : B.RawBandGauge)
    {Cscale Lscale CL1 w : ℝ}
    (hCscale : 0 ≤ Cscale) (hLscale : 0 < Lscale)
    (hphysical : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |(B.tiltedLaw xi).covariance
          (fun m ↦ B.nuisanceStatistic m NuisanceCoord.physical)
          (fun m ↦ valuation p.1 (B.sampleData.value m))| ≤
        (Cscale / Lscale) * (1 / (p.1 : ℝ)))
    (hpair : ∀ (p : BandPrime B.sampleData.n B.sampleData.W)
      (c c' : Cell Head),
      |((B.guardedCellProbability c).exponentialTilt
          (FiniteProbability.sigmaCellScore
            (B.scaledBridgeScore xi) c)).expect
          (fun x ↦ valuation p.1 (x : ℕ)) -
        ((B.guardedCellProbability c').exponentialTilt
          (FiniteProbability.sigmaCellScore
            (B.scaledBridgeScore xi) c')).expect
          (fun x ↦ valuation p.1 (x : ℕ))| ≤
        (Cscale / Lscale) * (1 / (p.1 : ℝ)))
    (hL1 : B.partition.compensatedL1 q ≤ CL1 * w) :
    ‖B.nuisanceCovarianceVector xi (B.postBandPrimeScore q)‖ ≤
      (Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
        ((6 * Cscale / Lscale) * CL1)) * w := by
  have hmarked :=
    B.nuisanceMarkedRows_le_of_pairwise_cell_valuation_and_physical
      xi hCscale hLscale hphysical hpair
  have hCmarked : 0 ≤ 6 * Cscale / Lscale := by positivity
  exact B.nuisanceCovarianceVector_postBand_norm_le_of_marked_and_l1
    xi q hCmarked hmarked hL1

/-- Relative common-profile errors attach to the normalized head row without
losing the moving low-band mass.  This is the exact finite aggregation used
for the head part of the Lemma 8.6 nuisance cross-row. -/
theorem abs_normalizedBandCovarianceRow_headFunction_le
    [Nonempty Head]
    (xi : B.ParamSpace) (phi : Head → ℝ)
    (main : Band → ℝ) {epsilon K : ℝ}
    (hepsilon : 0 ≤ epsilon) (hK : 0 ≤ K)
    (hphi : ∀ h, |phi h| ≤ K)
    (hcell : ∀ (c : Cell Head) (j : Band),
      |((B.guardedCellProbability c).exponentialTilt
          (FiniteProbability.sigmaCellScore
            (B.scaledBridgeScore xi) c)).expect
          (fun x ↦ B.bandScore j ⟨c, x⟩) - main j| ≤
        epsilon * B.harmonicMass j)
    (j : Band) :
    |B.normalizedBandCovarianceRow xi (B.headFunctionScore phi) j| ≤
      2 * K * epsilon := by
  have hmass : 0 < B.harmonicMass j := B.harmonicMass_pos j
  have herror : 0 ≤ epsilon * B.harmonicMass j :=
    mul_nonneg hepsilon hmass.le
  have hcov :=
    B.abs_tiltedLaw_covariance_headFunction_le_of_common_cell_expect
      xi (B.bandScore j) phi (main j)
      (epsilon * B.harmonicMass j) K herror hK hphi
      (fun c ↦ hcell c j)
  unfold normalizedBandCovarianceRow
  rw [abs_div, abs_of_pos hmass]
  calc
    |(B.tiltedLaw xi).covariance (B.bandScore j)
        (B.headFunctionScore phi)| / B.harmonicMass j ≤
      (2 * K * (epsilon * B.harmonicMass j)) /
        B.harmonicMass j :=
      div_le_div_of_nonneg_right hcov hmass.le
    _ = 2 * K * epsilon := by field_simp

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
