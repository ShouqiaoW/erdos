import Erdos390.Full.ConditionedPoissonLimit
import Erdos390.Full.PalmDisintegrationLogic

/-!
# Closing the Poisson--Dickman kernel argument from genuine Palm identities

This file composes the analytic and null-set bookkeeping layers.  Its main
theorem states precisely what remains to be obtained from the actual
conditioned process: one- and two-mark identities under the same nonzero
residual law.  Given those identities, an `L²(dt/t)` null vector of the
Poisson--Dickman covariance operator is almost everywhere a multiple of the
scale function.

No conditional law or Palm identity is postulated globally.  They appear as
arguments of the theorem so that the outstanding probability-theoretic
construction cannot be mistaken for a completed part of the formalization.
-/

open Filter Set
open scoped Interval

noncomputable section

namespace Erdos390.Full.PoissonDickmanKernelClosure

open MeasureTheory
open ConditionedPoissonLimit PalmDisintegrationLogic

private lemma ae_eq_on_Ioc_of_ae_eq_restrict {f g : ℝ → ℝ}
    (hfg : f =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] g) :
    ∀ᵐ x ∂volume, x ∈ Ioc (0 : ℝ) 1 → f x = g x := by
  exact (ae_restrict_iff' measurableSet_Ioc).1 hfg

/-- Localized same-residual comparison on the only totals used by the
positive Cauchy triangle.  This avoids requiring a conditional residual law
or a Palm identity at irrelevant real totals. -/
private lemma same_residual_ae_forces_additivity_Ioc
    {Omega : Type*} [MeasurableSpace Omega]
    (residual : ℝ → Measure Omega)
    (hresidual : ∀ u ∈ Ioc (0 : ℝ) 1, residual u ≠ 0)
    (Z : ℝ → Omega → ℝ) (f : ℝ → ℝ)
    (hone : ∀ᵐ u ∂volume, u ∈ Ioc (0 : ℝ) 1 →
      ∀ᵐ omega ∂residual u, Z u omega + f u = 0)
    (hpair : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
      z ∈ localCauchyTriangle →
        ∀ᵐ omega ∂residual (z.1 + z.2),
          Z (z.1 + z.2) omega + f z.1 + f z.2 = 0) :
    ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
      z ∈ localCauchyTriangle →
        f z.1 + f z.2 = f (z.1 + z.2) := by
  have hone' : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
      z.1 + z.2 ∈ Ioc (0 : ℝ) 1 →
        ∀ᵐ omega ∂residual (z.1 + z.2),
          Z (z.1 + z.2) omega + f (z.1 + z.2) = 0 :=
    ae_add_pullback hone
  have hsumNe : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
      z.1 + z.2 ≠ 0 :=
    ae_add_pullback (Measure.ae_ne volume 0)
  filter_upwards [hpair, hone', hsumNe] with z hzpair hzone hzne
  intro hz
  have hsumMem : z.1 + z.2 ∈ Ioc (0 : ℝ) 1 := by
    exact ⟨lt_of_le_of_ne (add_nonneg hz.1 hz.2.1) (Ne.symm hzne), hz.2.2⟩
  have hp := hzpair hz
  have ho := hzone hsumMem
  letI : (ae (residual (z.1 + z.2))).NeBot :=
    ae_neBot.mpr (hresidual (z.1 + z.2) hsumMem)
  obtain ⟨omega, hpomega, hoomega⟩ := (hp.and ho).exists
  linarith

/-- A weighted kernel-null vector is a scale multiple once the genuine Palm
disintegrations provide the one-mark and two-mark identities under one common
nonzero residual law.  All transfers across exceptional sets, including the
pullback by `(r,s) ↦ r+s`, are discharged in the proof. -/
theorem ae_eq_smul_id_of_weightedKernelNull_of_palm
    {Omega : Type*} [MeasurableSpace Omega]
    (f : ℝ → ℝ)
    (hfmeas : AEStronglyMeasurable f
      (volume.restrict (Ioc (0 : ℝ) 1)))
    (hsq : IntervalIntegrable (fun t : ℝ => f t ^ 2 / t)
      volume (0 : ℝ) 1)
    (hzero : ∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) 1),
      covarianceOperator f s = 0)
    (residual : ℝ → Measure Omega)
    (hresidual : ∀ u ∈ Ioc (0 : ℝ) 1, residual u ≠ 0)
    (Z : ℝ → Omega → ℝ)
    (hone : ∀ᵐ u ∂volume, u ∈ Ioc (0 : ℝ) 1 →
      ∀ᵐ omega ∂residual u, Z u omega + f u = 0)
    (hpair : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
      z ∈ localCauchyTriangle →
        ∀ᵐ omega ∂residual (z.1 + z.2),
          Z (z.1 + z.2) omega + f z.1 + f z.2 = 0) :
    ∃ lambda : ℝ,
      f =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)]
        fun t => lambda * t := by
  obtain ⟨g, hgcont, hfg⟩ :=
    exists_continuousRepresentative_of_weightedSquare_operator_ae_zero
      f hfmeas hsq hzero
  have haddf : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
      z ∈ localCauchyTriangle →
        f z.1 + f z.2 = f (z.1 + z.2) :=
    same_residual_ae_forces_additivity_Ioc residual hresidual Z f hone hpair
  have hfgFull : ∀ᵐ x ∂volume,
      x ∈ Ioc (0 : ℝ) 1 → f x = g x :=
    ae_eq_on_Ioc_of_ae_eq_restrict hfg
  have hfgFst : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
      z.1 ∈ Ioc (0 : ℝ) 1 → f z.1 = g z.1 :=
    (Measure.quasiMeasurePreserving_fst (μ := volume) (ν := volume)).ae hfgFull
  have hfgSnd : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
      z.2 ∈ Ioc (0 : ℝ) 1 → f z.2 = g z.2 :=
    (Measure.quasiMeasurePreserving_snd (μ := volume) (ν := volume)).ae hfgFull
  have hfgAdd : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
      z.1 + z.2 ∈ Ioc (0 : ℝ) 1 →
        f (z.1 + z.2) = g (z.1 + z.2) :=
    ae_add_pullback hfgFull
  have hfstNe : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume, z.1 ≠ 0 :=
    (Measure.quasiMeasurePreserving_fst (μ := volume) (ν := volume)).ae
      (Measure.ae_ne volume 0)
  have hsndNe : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume, z.2 ≠ 0 :=
    (Measure.quasiMeasurePreserving_snd (μ := volume) (ν := volume)).ae
      (Measure.ae_ne volume 0)
  have haddg : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
      z ∈ localCauchyTriangle →
        g (z.1 + z.2) = g z.1 + g z.2 := by
    filter_upwards [haddf, hfgFst, hfgSnd, hfgAdd, hfstNe, hsndNe] with
      z hzadd hzfst hzsnd hzsum hzne hysne
    intro hz
    have hxmem : z.1 ∈ Ioc (0 : ℝ) 1 := by
      exact ⟨lt_of_le_of_ne hz.1 (Ne.symm hzne),
        (le_add_of_nonneg_right hz.2.1).trans hz.2.2⟩
    have hymem : z.2 ∈ Ioc (0 : ℝ) 1 := by
      exact ⟨lt_of_le_of_ne hz.2.1 (Ne.symm hysne),
        (le_add_of_nonneg_left hz.1).trans hz.2.2⟩
    have hsumMem : z.1 + z.2 ∈ Ioc (0 : ℝ) 1 := by
      exact ⟨add_pos_of_pos_of_nonneg hxmem.1 hz.2.1, hz.2.2⟩
    calc
      g (z.1 + z.2) = f (z.1 + z.2) := (hzsum hsumMem).symm
      _ = f z.1 + f z.2 := (hzadd hz).symm
      _ = g z.1 + g z.2 := by rw [hzfst hxmem, hzsnd hymem]
  have haddPointwise :=
    continuousOn_local_additivity_of_ae g hgcont haddg
  obtain ⟨lambda, hlinear⟩ :=
    continuousOn_local_additive_linear g hgcont haddPointwise
  refine ⟨lambda, ?_⟩
  filter_upwards [hfg, ae_restrict_mem measurableSet_Ioc] with t hft ht
  rw [hft]
  exact hlinear t ⟨ht.1.le, ht.2⟩

end Erdos390.Full.PoissonDickmanKernelClosure
