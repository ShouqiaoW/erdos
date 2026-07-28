import Erdos390.Full.PaperExactTwoStageOrdinaryFast
import Erdos390.Full.PaperProposition87SpeedRadius
import Erdos390.Full.PaperSelectedMeshSchurRateEventually

/-!
# Marked-row rates used after the Proposition 8.7 radius is fixed

The ordinary fast target loses the full harmonic mass `O(log L)`, whereas
the compensated slow row has no such loss.  The canonical marked-row rate
was deliberately proved with `epsilon n * log L n -> 0`; this file checks
the two exact eventual estimates and keeps the choice of the ODE radius
strictly before the ambient threshold.
-/

open scoped BigOperators
open Filter Topology

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]

/-- The literal sum of arithmetic band masses has the global `12 log L`
bound, uniformly over every bridge whose ambient integer and cutoff are the
displayed `n,W`. -/
theorem eventually_sum_harmonicMass_le_twelve_logL (W : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (B : BridgeData Head Band),
        B.sampleData.n = n → B.sampleData.W = W →
          (∑ j : Band, B.harmonicMass j) ≤
            12 * Real.log (Scale.L B.sampleData.n) := by
  filter_upwards [PrimeSums.eventually_bandReciprocalSum_le_logL W]
      with n hn
  intro B hBn hBW
  rw [B.sum_harmonicMass_eq_bandReciprocalSum, hBn, hBW]
  simpa only [hBn] using hn

/-- Algebraic comparison of the ordinary fast marked-row majorant with the
sharp rate `epsilon * log L`. -/
theorem fastMarkedRowMajorant_le_of_harmonicMass
    (B : BridgeData Head Band)
    {epsilon CinvOrd Tband logL droot : ℝ}
    (hepsilon : 0 ≤ epsilon) (hCinvOrd : 0 ≤ CinvOrd)
    (hTband : 0 ≤ Tband) (hdroot : 0 ≤ droot)
    (hdimension : Real.sqrt
      (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) ≤ droot)
    (hmass : (∑ j : Band, B.harmonicMass j) ≤ 12 * logL) :
    Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
        ((epsilon * (∑ j : Band, B.harmonicMass j)) *
          (CinvOrd * Tband)) ≤
      (12 * droot * CinvOrd * Tband) * (epsilon * logL) := by
  have hmassNonneg : 0 ≤ ∑ j : Band, B.harmonicMass j := by
    exact Finset.sum_nonneg fun j hj ↦ (B.harmonicMass_pos j).le
  have hepsMass : 0 ≤ epsilon *
      (∑ j : Band, B.harmonicMass j) :=
    mul_nonneg hepsilon hmassNonneg
  have hcoef : 0 ≤ droot * CinvOrd * Tband := by positivity
  have hcoefCompare :
      Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
          CinvOrd * Tband ≤ droot * CinvOrd * Tband := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hdimension hCinvOrd) hTband
  have hscaled :
      epsilon * (∑ j : Band, B.harmonicMass j) ≤
        epsilon * (12 * logL) :=
    mul_le_mul_of_nonneg_left hmass hepsilon
  calc
    Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
        ((epsilon * (∑ j : Band, B.harmonicMass j)) *
          (CinvOrd * Tband)) =
      (Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
        CinvOrd * Tband) *
          (epsilon * (∑ j : Band, B.harmonicMass j)) := by ring
    _ ≤ (droot * CinvOrd * Tband) *
          (epsilon * (∑ j : Band, B.harmonicMass j)) :=
      mul_le_mul_of_nonneg_right hcoefCompare hepsMass
    _ ≤ (droot * CinvOrd * Tband) * (epsilon * (12 * logL)) :=
      mul_le_mul_of_nonneg_left hscaled hcoef
    _ = _ := by ring

/-- Uniform eventual smallness of the ordinary fast nuisance row.  The
fixed reserve may depend on the radius already chosen, but it does not feed
back into that choice. -/
theorem eventually_fastMarkedRowMajorant_le
    (W : ℕ) (epsilon : ℕ → ℝ)
    (hepsilonNonneg : ∀ n, 0 ≤ epsilon n)
    (hepsilonRate : Tendsto
      (fun n : ℕ ↦ epsilon n * Real.log (Scale.L n))
        atTop (nhds 0))
    {CinvOrd Tband reserve : ℝ}
    (hCinvOrd : 0 ≤ CinvOrd) (hTband : 0 ≤ Tband)
    (hreserve : 0 < reserve) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (B : BridgeData Head Band),
        B.sampleData.n = n → B.sampleData.W = W →
        Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
            ((epsilon B.sampleData.n *
              (∑ j : Band, B.harmonicMass j)) *
                (CinvOrd * Tband)) ≤ reserve := by
  let droot : ℝ := nuisanceDimensionCeiling Head
  let K : ℝ := 12 * droot * CinvOrd * Tband
  have hsmall := eventually_const_mul_vanishing_rate_le
    (fun n : ℕ ↦ epsilon n * Real.log (Scale.L n)) K reserve
      hepsilonRate hreserve
  filter_upwards [eventually_sum_harmonicMass_le_twelve_logL
      (Head := Head) (Band := Band) W, hsmall] with n hmass hsmallN
  intro B hBn hBW
  have hmajor := fastMarkedRowMajorant_le_of_harmonicMass
    (droot := droot) B
    (hepsilonNonneg B.sampleData.n) hCinvOrd hTband
    (by exact Real.sqrt_nonneg _)
    (by simpa only [droot] using B.sqrt_nuisanceCoord_card_le_ceiling)
    (hmass B hBn hBW)
  have hsmallB :
      (12 * droot * CinvOrd * Tband) *
          (epsilon B.sampleData.n * Real.log (Scale.L B.sampleData.n)) ≤
        reserve := by
    simpa only [hBn, K] using hsmallN
  exact hmajor.trans hsmallB

/-- The compensated slow nuisance row has no harmonic loss.  Its marked
coefficient is eventually smaller than any fixed post-radius reserve. -/
theorem eventually_slowMarkedRowCoefficient_le
    (epsilon : ℕ → ℝ)
    (hepsilonNonneg : ∀ n, 0 ≤ epsilon n)
    (hepsilonRate : Tendsto
      (fun n : ℕ ↦ epsilon n * Real.log (Scale.L n))
        atTop (nhds 0))
    {CL1 reserve : ℝ} (hCL1 : 0 ≤ CL1) (hreserve : 0 < reserve) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (B : BridgeData Head Band), B.sampleData.n = n →
        Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
            (epsilon B.sampleData.n * CL1) ≤ reserve := by
  have hepsilon : Tendsto epsilon atTop (nhds 0) :=
    tendsto_zero_of_nonneg_mul_logL_zero epsilon
      hepsilonNonneg hepsilonRate
  let droot : ℝ := nuisanceDimensionCeiling Head
  have hscaled : Tendsto (fun n : ℕ ↦
      (droot * CL1) * epsilon n) atTop (nhds 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hepsilon
  have hevent := hscaled.eventually (eventually_le_nhds hreserve)
  filter_upwards [hevent] with n hn
  intro B hBn
  have hdimension : Real.sqrt
      (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) ≤ droot := by
    simpa only [droot] using B.sqrt_nuisanceCoord_card_le_ceiling
  have hepsCL1 : 0 ≤ epsilon B.sampleData.n * CL1 :=
    mul_nonneg (hepsilonNonneg B.sampleData.n) hCL1
  calc
    Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
        (epsilon B.sampleData.n * CL1) ≤
      droot * (epsilon B.sampleData.n * CL1) :=
        mul_le_mul_of_nonneg_right hdimension hepsCL1
    _ = (droot * CL1) * epsilon B.sampleData.n := by ring
    _ ≤ reserve := by simpa only [hBn] using hn

/-- Simultaneous post-radius reserves used by the unit nuisance-speed
estimate.  The positive floor `gammaFloor` is fixed only after the ODE
radius; both conclusions then follow by increasing the ambient integer.
The theorem is uniform over every canonical bridge with the displayed
ambient integer and cutoff. -/
theorem eventually_twoStageMarkedRowReserves
    (W : ℕ) (epsilon : ℕ → ℝ)
    (hepsilonNonneg : ∀ n, 0 ≤ epsilon n)
    (hepsilonRate : Tendsto
      (fun n : ℕ ↦ epsilon n * Real.log (Scale.L n))
        atTop (nhds 0))
    {CinvOrd Tband CL1 gammaFloor gammaSlow A : ℝ}
    (hCinvOrd : 0 ≤ CinvOrd) (hTband : 0 ≤ Tband)
    (hCL1 : 0 ≤ CL1) (hgammaFloor : 0 < gammaFloor)
    (hgammaSlow : 0 < gammaSlow) (hA : 0 ≤ A) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (B : BridgeData Head Band),
        B.sampleData.n = n → B.sampleData.W = W →
        Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
            ((epsilon B.sampleData.n *
              (∑ j : Band, B.harmonicMass j)) *
                (CinvOrd * Tband)) ≤ gammaFloor / 2 ∧
          Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
              (epsilon B.sampleData.n * CL1) ≤
            gammaFloor * gammaSlow / (2 * (1 + A)) := by
  have hfastReserve : 0 < gammaFloor / 2 := div_pos hgammaFloor (by norm_num)
  have hslowDen : 0 < 2 * (1 + A) := by positivity
  have hslowReserve :
      0 < gammaFloor * gammaSlow / (2 * (1 + A)) :=
    div_pos (mul_pos hgammaFloor hgammaSlow) hslowDen
  have hfast := eventually_fastMarkedRowMajorant_le
    (Head := Head) (Band := Band) W epsilon hepsilonNonneg
      hepsilonRate hCinvOrd hTband hfastReserve
  have hslow := eventually_slowMarkedRowCoefficient_le
    (Head := Head) (Band := Band) epsilon hepsilonNonneg
      hepsilonRate hCL1 hslowReserve
  filter_upwards [hfast, hslow] with n hfastN hslowN
  intro B hBn hBW
  exact ⟨hfastN B hBn hBW, hslowN B hBn⟩

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
