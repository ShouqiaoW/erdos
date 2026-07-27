import Erdos536.PrimeBandProfileConcrete
import Erdos536.PrimeBandBase

/-!
# Fixed shallow cells on the polynomial-cutoff quadratic band

This file supplies the generic fixed-depth facts used by the shallow
singleton-anchor construction.  A fixed depth cell has its expected
one-label intensity, and nested depth cells give nested subtype carriers.
-/

open scoped BigOperators
open Filter Topology

noncomputable section

namespace Erdos536

open PrimeSums
open PrimeBandTimeChange

/-- Fixed quadratic depth-cell intensity converges to one third of its
depth length. -/
theorem quadraticDepthBandCarrier_intensity_tendsto
    {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) :
    Tendsto
      (fun T : ℕ =>
        ∑ p ∈ quadraticDepthBandCarrier T r s,
          reciprocalBernoulli p.1 / 3)
      atTop (𝓝 ((s - r) / 3)) := by
  have hpow :
      Tendsto (fun T : ℕ => T ^ 2) atTop atTop :=
    tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)
  have hbase :=
    (depthBandOneThirdIntensity_tendsto hrs).comp hpow
  have hcutoff :=
    eventually_quadraticLowerCutoff_le_expEndpoint
      (depthCoordinate_pos s)
  have heq :
      (fun T : ℕ =>
        ∑ p ∈ quadraticDepthBandCarrier T r s,
          reciprocalBernoulli p.1 / 3) =ᶠ[atTop]
      (fun T : ℕ =>
        depthBandOneThirdIntensity (T ^ 2) r s) := by
    filter_upwards [hcutoff] with T hcutoffT
    exact quadraticDepthBandCarrier_intensity_eq
      hr hrs hcutoffT
  exact hbase.congr' heq.symm

/-- Eventual upper form of the fixed-cell intensity limit. -/
theorem eventually_quadraticDepthBandCarrier_intensity_lt
    {r s ε : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s)
    (hε : 0 < ε) :
    ∀ᶠ T : ℕ in atTop,
      (∑ p ∈ quadraticDepthBandCarrier T r s,
          reciprocalBernoulli p.1 / 3) <
        (s - r) / 3 + ε := by
  exact
    (quadraticDepthBandCarrier_intensity_tendsto hr hrs).eventually
      (Iio_mem_nhds (lt_add_of_pos_right _ hε))

/-- Eventual lower form of the fixed-cell intensity limit. -/
theorem eventually_quadraticDepthBandCarrier_intensity_gt
    {r s ε : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s)
    (hε : 0 < ε) :
    ∀ᶠ T : ℕ in atTop,
      (s - r) / 3 - ε <
        ∑ p ∈ quadraticDepthBandCarrier T r s,
          reciprocalBernoulli p.1 / 3 := by
  exact
    (quadraticDepthBandCarrier_intensity_tendsto hr hrs).eventually
      (Ioi_mem_nhds (sub_lt_self _ hε))

/-- Inclusion of nested fixed depth cells, already inside the common
quadratic-band subtype. -/
theorem quadraticDepthBandCarrier_mono
    {T : ℕ} {r₀ r₁ s₁ s₀ : ℝ}
    (hr : r₀ ≤ r₁) (hs : s₁ ≤ s₀) :
    quadraticDepthBandCarrier T r₁ s₁ ⊆
      quadraticDepthBandCarrier T r₀ s₀ := by
  intro p hp
  have hpInner :=
    mem_depthPrimeBand.mp
      (mem_quadraticDepthBandCarrier.mp hp)
  apply mem_quadraticDepthBandCarrier.mpr
  apply mem_depthPrimeBand.mpr
  refine ⟨hpInner.1, ?_, ?_⟩
  · have hcoord :=
      depthCoordinate_antitone hs
    have hendpoint :=
      expEndpoint_mono hcoord (T ^ 2)
    exact hendpoint.trans_lt hpInner.2.1
  · have hcoord :=
      depthCoordinate_antitone hr
    have hendpoint :=
      expEndpoint_mono hcoord (T ^ 2)
    exact hpInner.2.2.trans hendpoint

end Erdos536
