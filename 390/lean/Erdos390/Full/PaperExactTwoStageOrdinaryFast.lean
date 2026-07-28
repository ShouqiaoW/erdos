import Erdos390.Full.PaperExactTwoStageTargetSolve
import Erdos390.Full.PaperActualSchurMarkedRow

/-!
# Ordinary-fast / sharp-slow form of the exact two-stage solve

The fast target in Proposition 8.7 is bounded in the ordinary raw-band
supremum norm: its unprojected coordinates are
`(L / q) * Delta_j / H_j = O(1)`.  They are not, in general, bounded after
division by the moving centre `alpha_j`; in particular `alpha_0 -> 0`.

The slow regression is different.  Lemma 8.5 supplies a sharp inverse for
that right-hand side and hence a regression vector of size `O(w alpha_j)`.
This file records the exact finite algebra with those two norms kept
separate.  It is the norm-correct form of the block calculation in the
proof of Proposition 8.7.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticBandGeometry PaperWeightedInverseExport
  MovingLowGaugeTransfer

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- The denominator of the raw arithmetic gauge projection is exactly the
arithmetic centre energy used by the moving-low-cell estimates. -/
theorem sharpBandWeightTotal_eq_centerEnergy :
    sharpWeightTotal B.harmonicMass B.bandCenter =
      B.partition.centerEnergy := by
  unfold sharpWeightTotal sharpWeight harmonicMass bandCenter
    ArithmeticBandGeometry.Partition.centerEnergy
    Erdos390.Lemma84.WeightedBandData.centerEnergy
    Erdos390.Lemma84.WeightedBandData.bandNormSq
    Erdos390.Lemma84.WeightedBandData.bandInner
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Summing the literal band masses recovers the full reciprocal mass of
the actual prime band.  This exposes the sole `log L` loss in the ordinary
fast nuisance row. -/
theorem sum_harmonicMass_eq_bandReciprocalSum :
    (∑ j : Band, B.harmonicMass j) =
      PrimeSums.bandReciprocalSum B.sampleData.n B.sampleData.W := by
  calc
    (∑ j : Band, B.harmonicMass j) =
        ∑ p : BandPrime B.sampleData.n B.sampleData.W,
          (1 / (p.1 : ℝ)) := by
      unfold harmonicMass ArithmeticBandGeometry.Partition.mass
        Erdos390.Lemma84.WeightedBandData.mass
      rw [← Finset.sum_fiberwise Finset.univ B.partition.band
        (fun p : BandPrime B.sampleData.n B.sampleData.W ↦
          (1 / (p.1 : ℝ)))]
      apply Finset.sum_congr rfl
      intro j hj
      rfl
    _ = PrimeSums.bandReciprocalSum
        B.sampleData.n B.sampleData.W := by
      unfold PrimeSums.bandReciprocalSum
      have hattach := Finset.sum_attach
        (ArithmeticModel.primeBand B.sampleData.n B.sampleData.W)
        (fun p ↦ 1 / (p : ℝ))
      simpa only [Finset.univ_eq_attach] using hattach

/-- The rough-stage band envelope gives an ordinary, not sharp, bound for
the unprojected normalized target row. -/
theorem abs_normalizedTargetBandRow_le_of_envelopes
    [Nonempty Head]
    {C : ℝ} (Delta : Band → ℝ)
    (henv : B.HasTargetEnvelopes C Delta) (j : Band) :
    |B.normalizedTargetBandRow Delta j| ≤ C := by
  have hband := henv.1 j
  have hLq : 0 < B.L / B.q := div_pos B.L_pos B.q_pos
  have hqL : 0 < B.q / B.L := div_pos B.q_pos B.L_pos
  have hH : 0 < B.harmonicMass j := B.harmonicMass_pos j
  unfold normalizedTargetBandRow
  rw [abs_div, abs_mul, abs_of_pos hLq, abs_of_pos hH]
  calc
    (B.L / B.q) * |Delta j| / B.harmonicMass j ≤
        (B.L / B.q) *
            ((B.q / B.L) * C * |B.harmonicMass j|) /
          B.harmonicMass j := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hband hLq.le) hH.le
    _ = C := by
      rw [abs_of_pos hH]
      field_simp [B.L_pos.ne', B.q_pos.ne', hH.ne']

/-- The compensated scalar target coordinate has the same fixed envelope.
The division by `w` is cancelled by the sharper rough-stage scalar bound. -/
theorem abs_normalizedTarget_slow_le_of_envelopes
    [Nonempty Head]
    {C : ℝ} (Delta : Band → ℝ)
    (henv : B.HasTargetEnvelopes C Delta) :
    |B.mainPart (B.normalizedTarget Delta) MainCoord.slow| ≤ C := by
  have hslow := henv.2
  have hLq : 0 < B.L / B.q := div_pos B.L_pos B.q_pos
  have hqL : 0 < B.q / B.L := div_pos B.q_pos B.L_pos
  rw [B.mainPart_slow]
  rw [B.normalizedTarget_slow_apply]
  rw [abs_mul, abs_of_pos hLq, abs_div, abs_of_pos B.w_pos]
  calc
    (B.L / B.q) *
        (|∑ j, B.bandCenter j * Delta j| / B.w) ≤
      (B.L / B.q) *
        (((B.q / B.L) * C * B.w) / B.w) := by
      exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hslow B.w_pos.le) hLq.le
    _ = C := by
      field_simp [B.L_pos.ne', B.q_pos.ne', B.w_pos.ne']

/-- Exact ordinary projection estimate.  The sole geometric input is the
displayed ratio between the first band moment and
`sum_j H_j alpha_j^2`.  On a permitted regular mesh Lemma 8.4 bounds that
ratio uniformly by the fixed positive interior anchor block. -/
theorem projectRawBandVector_norm_le_of_moment_ratio
    [Nonempty Band]
    (x : Band → ℝ) {C R : ℝ}
    (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hx : ∀ j, |x j| ≤ C)
    (hRatio : (∑ j : Band,
        B.harmonicMass j * B.bandCenter j) ≤
      R * sharpWeightTotal B.harmonicMass B.bandCenter) :
    ‖B.projectRawBandVector x‖ ≤ (1 + R) * C := by
  let total : ℝ := sharpWeightTotal B.harmonicMass B.bandCenter
  let numerator : ℝ := ∑ j : Band,
    B.harmonicMass j * B.bandCenter j * x j
  have htotal : 0 < total := by
    simpa only [total] using B.sharpBandWeightTotal_pos
  have hmoment : 0 ≤ ∑ j : Band,
      B.harmonicMass j * B.bandCenter j := by
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (B.harmonicMass_pos j).le (B.bandCenter_pos j).le
  have hnum : |numerator| ≤
      C * ∑ j : Band, B.harmonicMass j * B.bandCenter j := by
    dsimp only [numerator]
    calc
      |∑ j : Band, B.harmonicMass j * B.bandCenter j * x j| ≤
          ∑ j : Band,
            |B.harmonicMass j * B.bandCenter j * x j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j : Band,
          C * (B.harmonicMass j * B.bandCenter j) := by
        apply Finset.sum_le_sum
        intro j hj
        rw [abs_mul, abs_mul, abs_of_pos (B.harmonicMass_pos j),
          abs_of_pos (B.bandCenter_pos j)]
        calc
          B.harmonicMass j * B.bandCenter j * |x j| ≤
              (B.harmonicMass j * B.bandCenter j) * C :=
            mul_le_mul_of_nonneg_left (hx j)
              (mul_nonneg (B.harmonicMass_pos j).le
                (B.bandCenter_pos j).le)
          _ = C * (B.harmonicMass j * B.bandCenter j) := by ring
      _ = C * ∑ j : Band,
          B.harmonicMass j * B.bandCenter j := by
        rw [Finset.mul_sum]
  have hmean : |numerator / total| ≤ C * R := by
    rw [abs_div, abs_of_pos htotal]
    calc
      |numerator| / total ≤
          (C * ∑ j : Band,
            B.harmonicMass j * B.bandCenter j) / total :=
        div_le_div_of_nonneg_right hnum htotal.le
      _ ≤ (C * (R * total)) / total := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hRatio hC) htotal.le
      _ = C * R := by field_simp [htotal.ne']
  have hbound : 0 ≤ (1 + R) * C :=
    mul_nonneg (by linarith) hC
  change ‖(B.projectRawBandVector x).1‖ ≤ (1 + R) * C
  rw [pi_norm_le_iff_of_nonneg hbound]
  intro j
  rw [Real.norm_eq_abs]
  change |weightedGaugeProjection B.harmonicMass B.bandCenter x j| ≤ _
  unfold weightedGaugeProjection
  change |x j - B.bandCenter j * (numerator / total)| ≤ _
  calc
    |x j - B.bandCenter j * (numerator / total)| ≤
        |x j| + |B.bandCenter j| * |numerator / total| := by
      simpa only [abs_mul] using abs_sub (x j)
        (B.bandCenter j * (numerator / total))
    _ ≤ C + 1 * (C * R) := by
      have hcenter := (B.partition.center_mem_zero_one B.n_gt_one j).2
      rw [abs_of_pos (B.bandCenter_pos j)]
      exact add_le_add (hx j)
        (mul_le_mul hcenter hmean (abs_nonneg _) (by positivity))
    _ = (1 + R) * C := by ring

/-- Target-envelope version of the preceding projection estimate. -/
theorem projectedNormalizedTargetBand_norm_le_of_envelopes
    [Nonempty Head] [Nonempty Band]
    {C R : ℝ} (hC : 0 ≤ C) (hR : 0 ≤ R)
    (Delta : Band → ℝ) (henv : B.HasTargetEnvelopes C Delta)
    (hRatio : (∑ j : Band,
        B.harmonicMass j * B.bandCenter j) ≤
      R * sharpWeightTotal B.harmonicMass B.bandCenter) :
    ‖B.projectedNormalizedTargetBand Delta‖ ≤ (1 + R) * C := by
  exact B.projectRawBandVector_norm_le_of_moment_ratio
    (B.normalizedTargetBandRow Delta) hC hR
    (B.abs_normalizedTargetBandRow_le_of_envelopes Delta henv)
    hRatio

/-- Paper-facing ordinary target bound from separate first-moment and
center-energy estimates.  This is the form used on the moving-low mesh:
the numerator has a fixed upper bound while the positive interior cells
give a fixed lower bound for the sharp projection denominator.  No lower
bound for the vanishing low-cell centre is used. -/
theorem projectedNormalizedTargetBand_norm_le_of_envelopes_and_energy
    [Nonempty Head] [Nonempty Band]
    {C K kappa : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hkappa : 0 < kappa) (Delta : Band → ℝ)
    (henv : B.HasTargetEnvelopes C Delta)
    (hmoment : (∑ j : Band,
      B.harmonicMass j * B.bandCenter j) ≤ K)
    (henergy : kappa ≤
      sharpWeightTotal B.harmonicMass B.bandCenter) :
    ‖B.projectedNormalizedTargetBand Delta‖ ≤
      (1 + K / kappa) * C := by
  have hR : 0 ≤ K / kappa := div_nonneg hK hkappa.le
  have hRatio :
      (∑ j : Band, B.harmonicMass j * B.bandCenter j) ≤
        (K / kappa) *
          sharpWeightTotal B.harmonicMass B.bandCenter := by
    calc
      (∑ j : Band, B.harmonicMass j * B.bandCenter j) ≤ K := hmoment
      _ = (K / kappa) * kappa := by field_simp [hkappa.ne']
      _ ≤ (K / kappa) *
          sharpWeightTotal B.harmonicMass B.bandCenter :=
        mul_le_mul_of_nonneg_left henergy hR
  exact B.projectedNormalizedTargetBand_norm_le_of_envelopes
    hC hR Delta henv hRatio

/-- A reciprocal marked family controls an ordinary-bounded raw band score.
Unlike the sharp version, its finite factor is `sum_j H_j`; this is exactly
the `O(log L / L)` nuisance coefficient used for the fast target in the
paper. -/
theorem nuisanceCovarianceVector_rawBandRegression_norm_le_of_marked
    [Nonempty Head]
    (xi : B.ParamSpace)
    {Cmarked : ℝ} (hCmarked : 0 ≤ Cmarked)
    (hmarked : ∀ (c : NuisanceCoord B.HeadIndex)
      (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ ArithmeticModel.valuation p.1
          (B.sampleData.value m))| ≤
        Cmarked * (1 / (p.1 : ℝ)))
    (q : B.RawBandGauge) :
    ‖B.nuisanceCovarianceVector xi (B.bandRegressionScore q)‖ ≤
      Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
        ((Cmarked * ∑ j : Band, B.harmonicMass j) * ‖q‖) := by
  have hmass : 0 ≤ ∑ j : Band, B.harmonicMass j := by
    apply Finset.sum_nonneg
    intro j hj
    exact (B.harmonicMass_pos j).le
  have hK : 0 ≤ (Cmarked * ∑ j : Band, B.harmonicMass j) * ‖q‖ :=
    mul_nonneg (mul_nonneg hCmarked hmass) (norm_nonneg q)
  apply B.nuisanceCovarianceVector_norm_le_sqrt_card_mul
    xi (B.bandRegressionScore q) hK
  intro c
  let mu := B.tiltedLaw xi
  let Z : B.sampleData.Sample → ℝ :=
    fun m ↦ B.nuisanceStatistic m c
  have hsum :
      mu.covariance Z (B.bandRegressionScore q) =
        ∑ j : Band, q.1 j * mu.covariance Z (B.bandScore j) := by
    unfold bandRegressionScore
    rw [show (fun m ↦ ∑ j : Band, q.1 j * B.bandScore j m) =
      fun m ↦ ∑ j ∈ (Finset.univ : Finset Band),
        q.1 j * B.bandScore j m by simp]
    rw [mu.covariance_sum_right]
    apply Finset.sum_congr rfl
    intro j hj
    rw [mu.covariance_smul_right]
  change |mu.covariance Z (B.bandRegressionScore q)| ≤ _
  rw [hsum]
  calc
    |∑ j : Band, q.1 j * mu.covariance Z (B.bandScore j)| ≤
        ∑ j : Band, |q.1 j * mu.covariance Z (B.bandScore j)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Band, ‖q‖ * (Cmarked * B.harmonicMass j) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul]
      have hq : |q.1 j| ≤ ‖q‖ := by
        simpa only [Real.norm_eq_abs] using norm_le_pi_norm q.1 j
      exact mul_le_mul hq
        (B.abs_covariance_nuisance_bandScore_le_of_marked
          xi c j (fun p ↦ hmarked c p))
        (abs_nonneg _) (norm_nonneg q)
    _ = (Cmarked * ∑ j : Band, B.harmonicMass j) * ‖q‖ := by
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      ring

/-- The ordinary inverse and ordinary target bound discharge the fast
nuisance covariance row from the same reciprocal marked family. -/
theorem targetFast_nuisanceCovarianceVector_norm_le_of_marked_ordinary
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace)
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    {Cmarked CinvOrd Tband : ℝ}
    (hCmarked : 0 ≤ Cmarked) (hCinvOrd : 0 ≤ CinvOrd)
    (hinvOrd : ∀ v, ‖e.symm v‖ ≤ CinvOrd * ‖v‖)
    (Delta : Band → ℝ)
    (htargetBand : ‖B.projectedNormalizedTargetBand Delta‖ ≤ Tband)
    (hmarked : ∀ (c : NuisanceCoord B.HeadIndex)
      (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ ArithmeticModel.valuation p.1
          (B.sampleData.value m))| ≤
        Cmarked * (1 / (p.1 : ℝ))) :
    ‖B.nuisanceCovarianceVector xi
        (B.bandRegressionScore
          (e.symm (B.projectedNormalizedTargetBand Delta)))‖ ≤
      Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
        ((Cmarked * ∑ j : Band, B.harmonicMass j) *
          (CinvOrd * Tband)) := by
  have hq : ‖e.symm (B.projectedNormalizedTargetBand Delta)‖ ≤
      CinvOrd * Tband :=
    (hinvOrd _).trans
      (mul_le_mul_of_nonneg_left htargetBand hCinvOrd)
  have hraw := B.nuisanceCovarianceVector_rawBandRegression_norm_le_of_marked
    xi hCmarked hmarked
      (e.symm (B.projectedNormalizedTargetBand Delta))
  have hmass : 0 ≤ ∑ j : Band, B.harmonicMass j := by
    apply Finset.sum_nonneg
    intro j hj
    exact (B.harmonicMass_pos j).le
  exact hraw.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hq (mul_nonneg hCmarked hmass))
    (Real.sqrt_nonneg _))

/-- The two nuisance covariance rows needed by the exact two-stage solve
come from one literal marked-prime estimate.  The fast row uses the
ordinary inverse because its target is only bounded in raw sup norm; the
slow row uses the already proved compensated `L¹` estimate.  Thus neither
row is an independent analytic contract in Proposition 8.7. -/
theorem twoStage_nuisanceCovarianceRows_le_of_marked
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    {Cmarked CinvOrd Tband CL1 : ℝ}
    (hCmarked : 0 ≤ Cmarked) (hCinvOrd : 0 ≤ CinvOrd)
    (hinvOrd : ∀ v, ‖e.symm v‖ ≤ CinvOrd * ‖v‖)
    (Delta : Band → ℝ)
    (htargetBand : ‖B.projectedNormalizedTargetBand Delta‖ ≤ Tband)
    (hmarked : ∀ (c : NuisanceCoord B.HeadIndex)
      (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ ArithmeticModel.valuation p.1
          (B.sampleData.value m))| ≤
          Cmarked * (1 / (p.1 : ℝ)))
    (hL1 : B.partition.compensatedL1
      (B.actualBandRegression xi hgamma hgap e) ≤ CL1 * B.w) :
    ‖B.nuisanceCovarianceVector xi
        (B.bandRegressionScore
          (e.symm (B.projectedNormalizedTargetBand Delta)))‖ ≤
        Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
          ((Cmarked * (∑ j : Band, B.harmonicMass j)) *
            (CinvOrd * Tband)) ∧
      ‖B.nuisanceCovarianceVector xi
        (B.postBandPrimeScore
          (B.actualBandRegression xi hgamma hgap e))‖ ≤
        (Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
          (Cmarked * CL1)) * B.w := by
  constructor
  · exact B.targetFast_nuisanceCovarianceVector_norm_le_of_marked_ordinary
      xi e hCmarked hCinvOrd hinvOrd Delta htargetBand hmarked
  · exact B.nuisanceCovarianceVector_postBand_norm_le_of_marked_and_l1
      xi (B.actualBandRegression xi hgamma hgap e)
      hCmarked hmarked hL1

/-- The post-radius marked-row estimates in Proposition 8.7 realize the
two fixed nuisance reserves used by the noncircular speed choice. -/
theorem twoStage_nuisanceCovarianceRows_le_halfReserves
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gammaN : ℝ} (hgammaN : 0 < gammaN)
    (hgap : ∀ z, gammaN * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    {Cmarked CinvOrd Tband CL1 gammaSlow A : ℝ}
    (hCmarked : 0 ≤ Cmarked) (hCinvOrd : 0 ≤ CinvOrd)
    (hinvOrd : ∀ v, ‖e.symm v‖ ≤ CinvOrd * ‖v‖)
    (Delta : Band → ℝ)
    (htargetBand : ‖B.projectedNormalizedTargetBand Delta‖ ≤ Tband)
    (hmarked : ∀ (c : NuisanceCoord B.HeadIndex)
      (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ ArithmeticModel.valuation p.1
          (B.sampleData.value m))| ≤
          Cmarked * (1 / (p.1 : ℝ)))
    (hL1 : B.partition.compensatedL1
      (B.actualBandRegression xi hgammaN hgap e) ≤ CL1 * B.w)
    (hfastReserve :
      Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
          ((Cmarked * (∑ j : Band, B.harmonicMass j)) *
            (CinvOrd * Tband)) ≤ gammaN / 2)
    (hslowReserve :
      Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
          (Cmarked * CL1) ≤
        gammaN * gammaSlow / (2 * (1 + A))) :
    ‖B.nuisanceCovarianceVector xi
        (B.bandRegressionScore
          (e.symm (B.projectedNormalizedTargetBand Delta)))‖ ≤
        gammaN * (1 / 2) ∧
      ‖B.nuisanceCovarianceVector xi
        (B.postBandPrimeScore
          (B.actualBandRegression xi hgammaN hgap e))‖ ≤
        gammaN * (gammaSlow * B.w / (2 * (1 + A))) := by
  obtain ⟨hfast, hslow⟩ :=
    B.twoStage_nuisanceCovarianceRows_le_of_marked
      xi hgammaN hgap e hCmarked hCinvOrd hinvOrd Delta
      htargetBand hmarked hL1
  constructor
  · exact hfast.trans (hfastReserve.trans_eq (by ring))
  · calc
      ‖B.nuisanceCovarianceVector xi
          (B.postBandPrimeScore
            (B.actualBandRegression xi hgammaN hgap e))‖ ≤
        (Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
          (Cmarked * CL1)) * B.w := hslow
      _ ≤ (gammaN * gammaSlow / (2 * (1 + A))) * B.w :=
        mul_le_mul_of_nonneg_right hslowReserve B.w_pos.le
      _ = gammaN * (gammaSlow * B.w / (2 * (1 + A))) := by ring

/-- Mixed pairing estimate used by the target numerator: the regression
vector is sharp, while the projected fast target is only ordinary bounded.
The exact arithmetic first moment `sum_j H_j alpha_j` is retained. -/
theorem abs_bandDPairing_le_sharp_mul_raw
    [Nonempty Band]
    (q r : B.RawBandGauge) :
    |B.bandDPairing q r| ≤
      (∑ j : Band, B.harmonicMass j * B.bandCenter j) *
        paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one) q * ‖r‖ := by
  have hq (j : Band) :
      |q.1 j| ≤ B.bandCenter j *
        paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one) q := by
    have h := abs_raw_coordinate_le_paperSharpNorm
      B.harmonicMass B.bandCenter
      (B.partition.center_ne_zero B.n_gt_one) q j
    simpa only [abs_of_pos (B.bandCenter_pos j)] using h
  have hr (j : Band) : |r.1 j| ≤ ‖r‖ := by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm r.1 j
  have hsharp : 0 ≤ paperSharpNorm B.harmonicMass B.bandCenter
      (B.partition.center_ne_zero B.n_gt_one) q := norm_nonneg _
  have hrnorm : 0 ≤ ‖r‖ := norm_nonneg _
  calc
    |B.bandDPairing q r| ≤
        ∑ j : Band, |B.harmonicMass j * q.1 j * r.1 j| := by
      unfold bandDPairing
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Band,
        (B.harmonicMass j * B.bandCenter j) *
          paperSharpNorm B.harmonicMass B.bandCenter
            (B.partition.center_ne_zero B.n_gt_one) q * ‖r‖ := by
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul, abs_mul, abs_of_pos (B.harmonicMass_pos j)]
      have hleft : 0 ≤ B.harmonicMass j := (B.harmonicMass_pos j).le
      calc
        B.harmonicMass j * |q.1 j| * |r.1 j| ≤
            B.harmonicMass j *
                (B.bandCenter j *
                  paperSharpNorm B.harmonicMass B.bandCenter
                    (B.partition.center_ne_zero B.n_gt_one) q) *
              ‖r‖ := by
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left (hq j) hleft)
            (hr j) (abs_nonneg _)
            (mul_nonneg hleft
              (mul_nonneg (B.bandCenter_pos j).le hsharp))
        _ = (B.harmonicMass j * B.bandCenter j) *
              paperSharpNorm B.harmonicMass B.bandCenter
                (B.partition.center_ne_zero B.n_gt_one) q * ‖r‖ := by
          ring
    _ = (∑ j : Band, B.harmonicMass j * B.bandCenter j) *
          paperSharpNorm B.harmonicMass B.bandCenter
            (B.partition.center_ne_zero B.n_gt_one) q * ‖r‖ := by
      rw [Finset.sum_mul, Finset.sum_mul]

/-- Ordinary raw-sup fast-coordinate estimate from the ordinary inverse.
This is the exact finite version of (8.59). -/
theorem fastGauge_norm_le_of_ordinary_inverse
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (he : ∀ q, e q = B.actualBandSchurLinearMap xi hgamma hgap q)
    {Cinv : ℝ}
    (hinv : ∀ v, ‖e.symm v‖ ≤ Cinv * ‖v‖)
    (Delta : Band → ℝ) (u : B.MainSpace)
    (hu : B.exactSchurCovarianceOperator xi hgamma hgap u =
      B.mainPart (B.normalizedTarget Delta)) :
    ‖B.fastGaugeOfMain xi hgamma hgap e u‖ ≤
      Cinv * ‖B.projectedNormalizedTargetBand Delta‖ := by
  rw [B.fastGauge_eq_inverse_projectedTarget
    xi hgamma hgap e he Delta u hu]
  exact hinv _

/-- The target numerator with the norm split used in the paper. -/
def twoStageCompensatedTargetBoundOrdinaryFast
    (Creg Tband TslowCoord : ℝ) : ℝ :=
  (∑ j : Band, B.harmonicMass j * B.bandCenter j) *
      (Creg * B.w) * Tband +
    B.w * TslowCoord

/-- A sharp slow-regression estimate and an ordinary fast-target estimate
bound the compensated scalar target.  No division of the fast target by
`alpha_0` occurs. -/
theorem abs_compensatedNormalizedTarget_le_of_regression_ordinaryTarget
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (Delta : Band → ℝ)
    {Creg Tband TslowCoord : ℝ}
    (hCreg : 0 ≤ Creg)
    (hreg : paperSharpNorm B.harmonicMass B.bandCenter
      (B.partition.center_ne_zero B.n_gt_one)
      (B.actualBandRegression xi hgamma hgap e) ≤ Creg * B.w)
    (htargetBand : ‖B.projectedNormalizedTargetBand Delta‖ ≤ Tband)
    (htargetSlowCoord :
      |B.mainPart (B.normalizedTarget Delta) MainCoord.slow| ≤
        TslowCoord) :
    |B.compensatedNormalizedTarget xi hgamma hgap e Delta| ≤
      B.twoStageCompensatedTargetBoundOrdinaryFast
        Creg Tband TslowCoord := by
  unfold twoStageCompensatedTargetBoundOrdinaryFast
  rw [B.compensatedNormalizedTarget_eq_slow_sub_bandDPairing]
  have hD := B.abs_bandDPairing_le_sharp_mul_raw
    (B.actualBandRegression xi hgamma hgap e)
    (B.projectedNormalizedTargetBand Delta)
  have hmoment : 0 ≤ ∑ j : Band,
      B.harmonicMass j * B.bandCenter j := by
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (B.harmonicMass_pos j).le (B.bandCenter_pos j).le
  have hregNonneg : 0 ≤ Creg * B.w :=
    mul_nonneg hCreg B.w_pos.le
  have hD' :
      |B.bandDPairing (B.actualBandRegression xi hgamma hgap e)
          (B.projectedNormalizedTargetBand Delta)| ≤
        (∑ j : Band, B.harmonicMass j * B.bandCenter j) *
          (Creg * B.w) * Tband := by
    calc
      |B.bandDPairing (B.actualBandRegression xi hgamma hgap e)
          (B.projectedNormalizedTargetBand Delta)| ≤
        (∑ j : Band, B.harmonicMass j * B.bandCenter j) *
          paperSharpNorm B.harmonicMass B.bandCenter
            (B.partition.center_ne_zero B.n_gt_one)
            (B.actualBandRegression xi hgamma hgap e) *
          ‖B.projectedNormalizedTargetBand Delta‖ := hD
      _ ≤ (∑ j : Band, B.harmonicMass j * B.bandCenter j) *
          (Creg * B.w) * Tband := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hreg hmoment)
          htargetBand (norm_nonneg _)
          (mul_nonneg hmoment hregNonneg)
  calc
    |-B.bandDPairing (B.actualBandRegression xi hgamma hgap e)
          (B.projectedNormalizedTargetBand Delta) +
        B.w * B.mainPart (B.normalizedTarget Delta) MainCoord.slow| ≤
      |B.bandDPairing (B.actualBandRegression xi hgamma hgap e)
          (B.projectedNormalizedTargetBand Delta)| +
        B.w * |B.mainPart (B.normalizedTarget Delta) MainCoord.slow| := by
      calc
        _ ≤ |-B.bandDPairing
              (B.actualBandRegression xi hgamma hgap e)
              (B.projectedNormalizedTargetBand Delta)| +
            |B.w * B.mainPart (B.normalizedTarget Delta)
              MainCoord.slow| := abs_add_le _ _
        _ = _ := by rw [abs_neg, abs_mul, abs_of_pos B.w_pos]
    _ ≤ (∑ j : Band, B.harmonicMass j * B.bandCenter j) *
          (Creg * B.w) * Tband + B.w * TslowCoord :=
      add_le_add hD'
        (mul_le_mul_of_nonneg_left htargetSlowCoord B.w_pos.le)

/-- Prime-fugacity estimate with an ordinary fast vector and the sharp
compensated slow coefficient estimate. -/
theorem effectivePrimeVelocity_norm_le_of_ordinaryFast_compensated
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (u : B.MainSpace)
    {Cfast Clambda Ccomp : ℝ}
    (hCfast : 0 ≤ Cfast) (hClambda : 0 ≤ Clambda)
    (hCcomp : 0 ≤ Ccomp)
    (hfast : ‖B.fastGaugeOfMain xi hgamma hgap e u‖ ≤ Cfast)
    (hlambda : |u MainCoord.slow / B.w| ≤ Clambda)
    (hcomp : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |B.actualCompensatedCoefficient
        (B.actualBandRegression xi hgamma hgap e) p| ≤ Ccomp) :
    ‖fun p : BandPrime B.sampleData.n B.sampleData.W =>
        (B.rawGaugeOfMain u).1 (B.partition.band p) +
          (u MainCoord.slow / B.w) * B.primeDeviation p‖ ≤
      Cfast + Clambda * Ccomp := by
  have hbound : 0 ≤ Cfast + Clambda * Ccomp :=
    add_nonneg hCfast (mul_nonneg hClambda hCcomp)
  rw [pi_norm_le_iff_of_nonneg hbound]
  intro p
  rw [Real.norm_eq_abs,
    B.effectivePrimeCoefficient_fast_compensated xi hgamma hgap e u p]
  have hq :
      |(B.fastGaugeOfMain xi hgamma hgap e u).1
          (B.partition.band p)| ≤ Cfast := by
    calc
      |(B.fastGaugeOfMain xi hgamma hgap e u).1
          (B.partition.band p)| ≤
          ‖B.fastGaugeOfMain xi hgamma hgap e u‖ := by
        simpa only [Real.norm_eq_abs] using norm_le_pi_norm
          (B.fastGaugeOfMain xi hgamma hgap e u).1
          (B.partition.band p)
      _ ≤ Cfast := hfast
  calc
    |(B.fastGaugeOfMain xi hgamma hgap e u).1
          (B.partition.band p) +
        (u MainCoord.slow / B.w) *
          B.actualCompensatedCoefficient
            (B.actualBandRegression xi hgamma hgap e) p| ≤
      |(B.fastGaugeOfMain xi hgamma hgap e u).1
          (B.partition.band p)| +
        |u MainCoord.slow / B.w| *
          |B.actualCompensatedCoefficient
            (B.actualBandRegression xi hgamma hgap e) p| := by
      simpa only [abs_mul] using
        abs_add_le
          ((B.fastGaugeOfMain xi hgamma hgap e u).1
            (B.partition.band p))
          ((u MainCoord.slow / B.w) *
            B.actualCompensatedCoefficient
              (B.actualBandRegression xi hgamma hgap e) p)
    _ ≤ Cfast + Clambda * Ccomp :=
      add_le_add hq
        (mul_le_mul hlambda (hcomp p) (abs_nonneg _) hClambda)

/-- Norm-correct three-component estimate for Proposition 8.7.  The same
literal Schur equivalence carries an ordinary inverse estimate for the fast
target and a sharp inverse estimate for the slow regression. -/
theorem exactSchur_solution_component_bounds_of_ordinaryFast_twoStageTargets
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (he : ∀ q, e q = B.actualBandSchurLinearMap xi hgamma hgap q)
    (Delta : Band → ℝ)
    {CinvOrd Tband Vlower Tslow Ccomp
      CfastNuisance CslowNuisance : ℝ}
    (hCinvOrd : 0 ≤ CinvOrd) (hTband : 0 ≤ Tband)
    (hVlower : 0 < Vlower) (hTslow : 0 ≤ Tslow)
    (hCcomp : 0 ≤ Ccomp)
    (hinvOrd : ∀ v, ‖e.symm v‖ ≤ CinvOrd * ‖v‖)
    (htargetBand : ‖B.projectedNormalizedTargetBand Delta‖ ≤ Tband)
    (hvariance : Vlower ≤ B.actualTwoStageCompensatedVariance
      xi hgamma hgap e)
    (htargetSlow : |B.compensatedNormalizedTarget
      xi hgamma hgap e Delta| ≤ Tslow)
    (hcomp : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |B.actualCompensatedCoefficient
        (B.actualBandRegression xi hgamma hgap e) p| ≤ Ccomp)
    (hfastNuisance : ‖B.targetFastNuisanceCoefficient
      xi hgamma hgap e Delta‖ ≤ CfastNuisance)
    (hslowNuisance : ‖B.actualTwoStageNuisanceCoefficient
      xi hgamma hgap e‖ ≤ CslowNuisance)
    (u : B.MainSpace)
    (hu : B.exactSchurCovarianceOperator xi hgamma hgap u =
      B.mainPart (B.normalizedTarget Delta)) :
    ‖fun p : BandPrime B.sampleData.n B.sampleData.W =>
        (B.rawGaugeOfMain u).1 (B.partition.band p) +
          (u MainCoord.slow / B.w) * B.primeDeviation p‖ ≤
        CinvOrd * Tband + (Tslow / Vlower) * Ccomp ∧
      ‖B.exactNuisanceRegression xi hgamma hgap u‖ ≤
        CfastNuisance + (Tslow / Vlower) * CslowNuisance ∧
      |u MainCoord.slow| ≤ B.w * (Tslow / Vlower) := by
  have hfast : ‖B.fastGaugeOfMain xi hgamma hgap e u‖ ≤
      CinvOrd * Tband := by
    calc
      ‖B.fastGaugeOfMain xi hgamma hgap e u‖ ≤
          CinvOrd * ‖B.projectedNormalizedTargetBand Delta‖ :=
        B.fastGauge_norm_le_of_ordinary_inverse
          xi hgamma hgap e he hinvOrd Delta u hu
      _ ≤ CinvOrd * Tband :=
        mul_le_mul_of_nonneg_left htargetBand hCinvOrd
  have hlambda : |u MainCoord.slow / B.w| ≤ Tslow / Vlower :=
    B.abs_slow_div_le_of_variance_target_bounds
      xi hgamma hgap e he Delta u hu hVlower hvariance
      hTslow htargetSlow
  have hClambda : 0 ≤ Tslow / Vlower :=
    div_nonneg hTslow hVlower.le
  have hprime := B.effectivePrimeVelocity_norm_le_of_ordinaryFast_compensated
    xi hgamma hgap e u
    (mul_nonneg hCinvOrd hTband) hClambda hCcomp hfast hlambda hcomp
  have hnuisance := B.exactNuisanceRegression_norm_le_of_twoStage
    xi hgamma hgap e he Delta u hu hClambda
      hfastNuisance hlambda hslowNuisance
  have hslow := B.abs_slow_le_of_variance_target_bounds
    xi hgamma hgap e he Delta u hu hVlower hvariance
      hTslow htargetSlow
  exact ⟨hprime, hnuisance, hslow⟩

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
