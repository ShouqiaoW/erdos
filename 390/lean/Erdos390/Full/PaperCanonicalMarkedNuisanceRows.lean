import Erdos390.Full.PaperCanonicalTiltedValuationMeanRows
import Erdos390.Full.PaperNuisancePrimeLogRows
import Erdos390.Full.PaperActualFullEffectiveBall

/-!
# Canonical marked nuisance rows on the effective ODE ball

The two canonical medium-law inputs are joined here: the Stieltjes physical
row and the pairwise full-valuation component profile.  The residual physical
tilt is inserted explicitly, and the exact finite-mixture decomposition then
produces every nuisance coordinate.  This is the global marked-row statement
used by the selected-mesh Schur argument.
-/

open Filter Topology Metric Set

namespace Erdos390.Full.PaperCanonicalMarkedNuisanceRows

open Erdos390.Full
open ArithmeticModel Scale HeadPattern StructuredCells
open ArithmeticBandGeometry PaperBridgeFit
open FiniteProbability PaperGuardCensus
open PaperCanonicalTiltedPrefixRows
open PaperCanonicalTiltedValuationMeanRows

noncomputable section

set_option maxHeartbeats 2400000

namespace PaperBridgeFit.BridgeData

open PaperBridgeFit

variable {Head : Type*} [Fintype Head] [DecidableEq Head]

/-- After `W` is fixed, every later effective ODE ball has one sharp marked
nuisance rate.  The rate is uniform in the canonical bridge, the point of the
closed ball, every nuisance coordinate, and every moving band prime.  There
is no premise relating the radius of the ball to `log W`. -/
theorem exists_uniform_canonical_tiltedLaw_nuisance_valuation_rate_on_effectiveBall
    [Nonempty Head]
    (P : Head → Pattern) (I : PhysicalIntervals) (U : ℝ)
    (_hU : 1 ≤ U)
    (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
    (hupperU : ∀ sigma, I.upper sigma ≤ U)
    (Cprom Cbank : ℕ) (G : ∀ n, Ledger n Cprom Cbank)
    (W : ℕ) (hW : 1 < W)
    (hHeadLe : ∀ h, ∀ p ∈ (P h).primes, p ≤ W)
    (a : NNReal) :
    ∃ epsilon : ℕ → ℝ,
      (∀ n, 0 ≤ epsilon n) ∧
      Tendsto (fun n : ℕ ↦ epsilon n * Real.log (L n))
        atTop (nhds 0) ∧
      ∃ N₀ : ℕ,
        ∀ {Band : Type*} [Fintype Band] [DecidableEq Band]
          (B : BridgeData Head Band) (z : B.EffectiveParamSpace),
          z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ) →
          N₀ ≤ B.sampleData.n → B.sampleData.W = W →
          (hsep : physicalBound (I.upper .minus) B.sampleData.n <
            physicalBound (I.lower .plus) B.sampleData.n) →
          (hremaining : ∀ c : Cell Head,
            (rawCell P I B.sampleData.n c \
              (G B.sampleData.n).guards).Nonempty) →
          B.sampleData = canonicalSampleData
            (W := B.sampleData.W) P I (G B.sampleData.n) hsep hremaining →
          ∀ (c : NuisanceCoord B.HeadIndex)
            (p : BandPrime B.sampleData.n B.sampleData.W),
            |(B.tiltedLaw (B.effectiveParamEquiv z)).covariance
                (fun m ↦ B.nuisanceStatistic m c)
                (fun m ↦ valuation p.1 (B.sampleData.value m))| ≤
              epsilon B.sampleData.n * (1 / (p.1 : ℝ)) := by
  let Acoef : ℝ := 3 * (a : ℝ)
  have hAcoef : 0 ≤ Acoef := by positivity
  obtain ⟨Aval, hAval0, epsilonMean, hepsilonMean0, hepsilonMeanRate,
      Nmean, hmean⟩ :=
    Erdos390.Full.PaperCanonicalTiltedValuationMeanRows.PaperBridgeFit.BridgeData.exists_uniform_canonical_cellMediumLaw_valuation_mean_profiles_rate_unrestricted
      P I Cprom Cbank G W hW hHeadLe Acoef hAcoef
  obtain ⟨epsilonPhysical, hepsilonPhysical0, hepsilonPhysicalRate,
      Nphysical, hphysical⟩ :=
    Erdos390.Full.PaperCanonicalTiltedPrefixRows.PaperBridgeFit.BridgeData.exists_uniform_canonical_cellMediumLaw_physical_valuation_rate_unrestricted
      P I Cprom Cbank G W hW hHeadLe Acoef hAcoef
  let structuralConstant : ℝ :=
    32 * Real.log U * Acoef * Real.log U * Aval +
      16 * Acoef * Real.log U * Aval
  let profileError : ℕ → ℝ := fun n ↦
    epsilonPhysical n + epsilonMean n + structuralConstant / L n
  let nuisanceFactor : ℝ := 6 * (1 + 2 * Real.log U)
  let epsilon : ℕ → ℝ := fun n ↦ nuisanceFactor * profileError n
  have hUstrict : 1 < U :=
    (hlowerOne .minus).trans_lt
      ((I.lower_lt_upper .minus).trans_le (hupperU .minus))
  have hlogU0 : 0 ≤ Real.log U := (Real.log_pos hUstrict).le
  have hstructural0 : 0 ≤ structuralConstant := by
    dsimp only [structuralConstant]
    positivity
  have hL0 : ∀ n : ℕ, 0 ≤ L n := by
    intro n
    cases n with
    | zero => norm_num [L]
    | succ n =>
      exact Real.log_nonneg (by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))
  have hprofile0 : ∀ n, 0 ≤ profileError n := by
    intro n
    dsimp only [profileError]
    exact add_nonneg
      (add_nonneg (hepsilonPhysical0 n) (hepsilonMean0 n))
      (div_nonneg hstructural0 (hL0 n))
  have hnuisanceFactor0 : 0 ≤ nuisanceFactor := by
    dsimp only [nuisanceFactor]
    positivity
  have hepsilon0 : ∀ n, 0 ≤ epsilon n := by
    intro n
    exact mul_nonneg hnuisanceFactor0 (hprofile0 n)
  have hLTop : Tendsto L atTop atTop := by
    simpa only [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlogLdivL : Tendsto (fun n : ℕ ↦ Real.log (L n) / L n)
      atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hLTop
  have hstructuralRate : Tendsto (fun n : ℕ ↦
      (structuralConstant / L n) * Real.log (L n))
      atTop (nhds 0) := by
    have hconst : Tendsto (fun _n : ℕ ↦ structuralConstant)
        atTop (nhds structuralConstant) := tendsto_const_nhds
    have hmul := hconst.mul hlogLdivL
    have hzero : Tendsto (fun n : ℕ ↦
        structuralConstant * (Real.log (L n) / L n))
        atTop (nhds 0) := by simpa only [mul_zero] using hmul
    apply hzero.congr'
    filter_upwards with n
    ring
  have hprofileRate : Tendsto (fun n : ℕ ↦
      profileError n * Real.log (L n)) atTop (nhds 0) := by
    have hsum :=
      (hepsilonPhysicalRate.add hepsilonMeanRate).add hstructuralRate
    simpa only [profileError, add_mul, zero_add] using hsum
  have hepsilonRate : Tendsto (fun n : ℕ ↦
      epsilon n * Real.log (L n)) atTop (nhds 0) := by
    have hconst : Tendsto (fun _n : ℕ ↦ nuisanceFactor)
        atTop (nhds nuisanceFactor) := tendsto_const_nhds
    have hmul := hconst.mul hprofileRate
    simpa only [epsilon, mul_zero, mul_assoc] using hmul
  have hsmallT : Tendsto (fun n : ℕ ↦
      8 * (Acoef * Real.log U / L n)) atTop (nhds 0) := by
    have hinv : Tendsto (fun n : ℕ ↦ (L n)⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp hLTop
    have hconst : Tendsto (fun _n : ℕ ↦ 8 * (Acoef * Real.log U))
        atTop (nhds (8 * (Acoef * Real.log U))) := tendsto_const_nhds
    have hmul := hconst.mul hinv
    have hzero : Tendsto (fun n : ℕ ↦
        (8 * (Acoef * Real.log U)) * (L n)⁻¹) atTop (nhds 0) := by
      simpa only [mul_zero] using hmul
    apply hzero.congr'
    filter_upwards with n
    rw [div_eq_mul_inv]
    ring
  have hsmallEvent : ∀ᶠ n : ℕ in atTop,
      8 * (Acoef * Real.log U / L n) ≤ 1 :=
    hsmallT.eventually (eventually_le_nhds (by norm_num))
  obtain ⟨Nsmall, hNsmall⟩ := Filter.eventually_atTop.mp hsmallEvent
  refine ⟨epsilon, hepsilon0, hepsilonRate,
    max Nmean (max Nphysical Nsmall), ?_⟩
  intro Band _instBand _instBandDec B z hz hN hBW hsep hremaining hcanonical
  let xi : B.ParamSpace := B.effectiveParamEquiv z
  have hNmean : Nmean ≤ B.sampleData.n := by omega
  have hNphysical : Nphysical ≤ B.sampleData.n := by omega
  have hNsmallBound : Nsmall ≤ B.sampleData.n := by omega
  have hznorm : ‖z‖ ≤ (a : ℝ) := by
    simpa only [mem_closedBall, dist_zero_right] using hz
  have hsize : B.paperEffectiveSize xi ≤ Acoef := by
    dsimp only [xi, Acoef]
    exact (B.paperEffectiveSize_effectiveParamEquiv_le z).trans
      (mul_le_mul_of_nonneg_left hznorm (by norm_num))
  have hbounds := B.effective_bounds_of_paperEffectiveSize xi hsize
  have heta : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |B.effectivePrimeCoefficient xi p| ≤ Acoef := hbounds.1
  have hnuisanceNorm : ‖B.nuisanceParameter xi‖ ≤ Acoef := hbounds.2
  have hphys : |xi MomentCoord.physical| ≤ Acoef := by
    calc
      |xi MomentCoord.physical| =
          ‖B.nuisanceParameter xi NuisanceCoord.physical‖ := by
        simp only [B.nuisanceParameter_physical, Real.norm_eq_abs]
      _ ≤ ‖B.nuisanceParameter xi‖ := by
        exact PiLp.norm_apply_le (B.nuisanceParameter xi)
          NuisanceCoord.physical
      _ ≤ Acoef := hnuisanceNorm
  have hmeanN := hmean B xi hNmean hBW heta hsep hremaining hcanonical
  have hphysicalN :=
    hphysical B xi hNphysical hBW heta hsep hremaining hcanonical
  have hsmall : 8 * (Acoef * Real.log U / B.L) ≤ 1 := by
    simpa only [BridgeData.L, Scale.L] using
      hNsmall B.sampleData.n hNsmallBound
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
  let Ccov : ℝ := B.L * epsilonPhysical B.sampleData.n
  let Cmean : ℝ := B.L * epsilonMean B.sampleData.n
  have hCcov : 0 ≤ Ccov :=
    mul_nonneg B.L_pos.le (hepsilonPhysical0 B.sampleData.n)
  have hCmean : 0 ≤ Cmean :=
    mul_nonneg B.L_pos.le (hepsilonMean0 B.sampleData.n)
  have hmediumCov : ∀ (p : BandPrime B.sampleData.n B.sampleData.W)
      (c : Cell Head),
      |(B.cellMediumLaw xi c).covariance
          (fun m ↦ valuation p.1 (m : ℕ))
          (fun m ↦ B.physicalScore ⟨c, m⟩)| ≤
        (Ccov / B.L) * (1 / (p.1 : ℝ)) := by
    intro p c
    calc
      _ ≤ epsilonPhysical B.sampleData.n / (p.1 : ℝ) :=
        hphysicalN p c
      _ = (Ccov / B.L) * (1 / (p.1 : ℝ)) := by
        dsimp only [Ccov]
        field_simp [B.L_pos.ne']
  have hmediumPair : ∀ (p : BandPrime B.sampleData.n B.sampleData.W)
      (c c' : Cell Head),
      |(B.cellMediumLaw xi c).expect
            (fun m ↦ valuation p.1 (m : ℕ)) -
        (B.cellMediumLaw xi c').expect
            (fun m ↦ valuation p.1 (m : ℕ))| ≤
        (Cmean / B.L) * (1 / (p.1 : ℝ)) := by
    intro p c c'
    calc
      _ ≤ epsilonMean B.sampleData.n / (p.1 : ℝ) :=
        (hmeanN p).2 c c'
      _ = (Cmean / B.L) * (1 / (p.1 : ℝ)) := by
        dsimp only [Cmean]
        field_simp [B.L_pos.ne']
  have hfullRaw := B.fullTiltCellProfiles_of_medium_stieltjes
    xi I hAcoef hAval0 hCcov hCmean hlowerOne hupperU hlo hhi hphys
    (fun p ↦ (hmeanN p).1) hsmall hmediumCov hmediumPair
  have hfull :
      (∀ (p : BandPrime B.sampleData.n B.sampleData.W) (c : Cell Head),
        |((B.guardedCellProbability c).exponentialTilt
            (sigmaCellScore (B.scaledBridgeScore xi) c)).covariance
            (fun m ↦ valuation p.1 (m : ℕ))
            (fun m ↦ B.physicalScore ⟨c, m⟩)| ≤
          profileError B.sampleData.n * (1 / (p.1 : ℝ))) ∧
      (∀ (p : BandPrime B.sampleData.n B.sampleData.W) (c c' : Cell Head),
        |((B.guardedCellProbability c).exponentialTilt
              (sigmaCellScore (B.scaledBridgeScore xi) c)).expect
              (fun m ↦ valuation p.1 (m : ℕ)) -
          ((B.guardedCellProbability c').exponentialTilt
              (sigmaCellScore (B.scaledBridgeScore xi) c')).expect
              (fun m ↦ valuation p.1 (m : ℕ))| ≤
            profileError B.sampleData.n * (1 / (p.1 : ℝ))) := by
    have hrewrite :
        (Ccov + Cmean +
            32 * Real.log U * Acoef * Real.log U * Aval +
            16 * Acoef * Real.log U * Aval) / B.L =
          profileError B.sampleData.n := by
      dsimp only [Ccov, Cmean, profileError]
      rw [show L B.sampleData.n = B.L by rfl]
      dsimp only [structuralConstant]
      field_simp [B.L_pos.ne']
      ring
    simpa only [hrewrite] using hfullRaw
  have hphysicalBound : ∀ m : B.sampleData.Sample,
      |B.physicalScore m| ≤ Real.log U :=
    B.abs_physicalScore_le_log_upperBound I hlowerOne hupperU hlo hhi
  have hmarked :=
    B.nuisanceMarkedRows_le_of_cell_physical_covariance_and_pairwise_valuation
      xi (Cscale := profileError B.sampleData.n) (Lscale := 1)
      (K := Real.log U) (hprofile0 B.sampleData.n) (by norm_num) hlogU0
      hphysicalBound
      (fun p c ↦ by simpa only [div_one] using hfull.1 p c)
      (fun p c c' ↦ by simpa only [div_one] using hfull.2 p c c')
  intro c p
  have hrow := hmarked c p
  simpa only [xi, epsilon, nuisanceFactor, div_one, mul_assoc] using hrow

end PaperBridgeFit.BridgeData

end

end Erdos390.Full.PaperCanonicalMarkedNuisanceRows
