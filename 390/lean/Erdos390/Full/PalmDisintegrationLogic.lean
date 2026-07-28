import Erdos390.Full.PoissonSelfSimilarity
import Mathlib.MeasureTheory.Group.Prod

/-!
# Null-set bookkeeping for Palm disintegration

The Poisson--Dickman kernel argument compares a two-mark Palm identity at
`(r,s)` with a one-mark identity at `r+s`.  Two measure-theoretic points are
made explicit here:

* a Lebesgue-null exceptional set in the total `u` pulls back to a null set
  under `(r,s) ↦ r+s`;
* if both identities use the same nonzero residual law, their almost-sure
  constants can be compared on one common sample.

Neither statement assumes the existence of the conditioned process; they are
the exact deterministic/filter logic to be used after the genuine Palm
disintegrations have been constructed.
-/

open Filter Set
open scoped ENNReal

noncomputable section

namespace Erdos390.Full.PalmDisintegrationLogic

open MeasureTheory

/-- Pulling a Lebesgue-a.e. assertion back by addition gives a product-
Lebesgue-a.e. assertion.  This is the rigorous form of the null-set pullback
used in the paper's one-mark/two-mark comparison. -/
lemma ae_add_pullback {P : ℝ → Prop} (hP : ∀ᵐ u ∂volume, P u) :
    ∀ᵐ z : ℝ × ℝ ∂volume.prod volume, P (z.1 + z.2) := by
  exact (MeasureTheory.quasiMeasurePreserving_add volume volume).ae hP

/-- Abstract same-residual-law comparison.  On a set `D` of mark pairs,
suppose the two-mark identity and the pulled-back one-mark identity both hold
almost surely under exactly `residual (r+s)`.  Since that measure is nonzero,
the two almost-sure events have a common point, and subtraction forces the
local Cauchy identity. -/
lemma same_residual_ae_forces_additivity
    {Omega : Type*} [MeasurableSpace Omega]
    (residual : ℝ → Measure Omega) (hresidual : ∀ u, residual u ≠ 0)
    (Z : ℝ → Omega → ℝ) (f : ℝ → ℝ) (D : Set (ℝ × ℝ))
    (hone : ∀ᵐ u ∂volume,
      ∀ᵐ omega ∂residual u, Z u omega + f u = 0)
    (hpair : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume, z ∈ D →
      ∀ᵐ omega ∂residual (z.1 + z.2),
        Z (z.1 + z.2) omega + f z.1 + f z.2 = 0) :
    ∀ᵐ z : ℝ × ℝ ∂volume.prod volume, z ∈ D →
      f z.1 + f z.2 = f (z.1 + z.2) := by
  have hone' : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
      ∀ᵐ omega ∂residual (z.1 + z.2),
        Z (z.1 + z.2) omega + f (z.1 + z.2) = 0 :=
    ae_add_pullback hone
  filter_upwards [hpair, hone'] with z hzpair hzone hzD
  have hp := hzpair hzD
  letI : (ae (residual (z.1 + z.2))).NeBot :=
    ae_neBot.mpr (hresidual (z.1 + z.2))
  obtain ⟨omega, hpomega, hoomega⟩ := (hp.and hzone).exists
  linarith

/-- The closed positive triangle on which local Cauchy additivity is needed. -/
def localCauchyTriangle : Set (ℝ × ℝ) :=
  {z | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 ≤ 1}

private lemma localCauchyTriangle_closed : IsClosed localCauchyTriangle := by
  change IsClosed
    ({z : ℝ × ℝ | (0 : ℝ) ≤ z.1} ∩
      ({z : ℝ × ℝ | (0 : ℝ) ≤ z.2} ∩
        {z : ℝ × ℝ | z.1 + z.2 ≤ (1 : ℝ)}))
  exact (isClosed_le continuous_const continuous_fst).inter
    ((isClosed_le continuous_const continuous_snd).inter
      (isClosed_le (continuous_fst.add continuous_snd) continuous_const))

private lemma localCauchyTriangle_convex : Convex ℝ localCauchyTriangle := by
  intro x hx y hy a b ha hb hab
  rcases hx with ⟨hx₁, hx₂, hxsum⟩
  rcases hy with ⟨hy₁, hy₂, hysum⟩
  change 0 ≤ (a • x + b • y).1 ∧
    0 ≤ (a • x + b • y).2 ∧
    (a • x + b • y).1 + (a • x + b • y).2 ≤ 1
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul]
  constructor
  · positivity
  constructor
  · positivity
  · nlinarith

private lemma localCauchyTriangle_interior_nonempty :
    (interior localCauchyTriangle).Nonempty := by
  let c : ℝ × ℝ := ((1 : ℝ) / 4, (1 : ℝ) / 4)
  let U : Set (ℝ × ℝ) :=
    Ioo ((1 : ℝ) / 8) ((3 : ℝ) / 8) ×ˢ
      Ioo ((1 : ℝ) / 8) ((3 : ℝ) / 8)
  have hUopen : IsOpen U := isOpen_Ioo.prod isOpen_Ioo
  have hcU : c ∈ U := by
    constructor <;> constructor <;> norm_num [c]
  have hUsub : U ⊆ localCauchyTriangle := by
    intro z hz
    rcases hz with ⟨hz₁, hz₂⟩
    exact ⟨by linarith [hz₁.1], by linarith [hz₂.1], by
      linarith [hz₁.2, hz₂.2]⟩
  refine ⟨c, (mem_interior_iff_mem_nhds).2 ?_⟩
  exact mem_of_superset (hUopen.mem_nhds hcU) hUsub

private lemma localCauchyTriangle_subset_closure_interior :
    localCauchyTriangle ⊆ closure (interior localCauchyTriangle) := by
  have heq := localCauchyTriangle_convex
    |>.closure_interior_eq_closure_of_nonempty_interior
      localCauchyTriangle_interior_nonempty
  rw [localCauchyTriangle_closed.closure_eq] at heq
  intro z hz
  rw [heq]
  exact hz

/-- If a continuous representative satisfies local additivity almost
everywhere on the positive triangle, then it satisfies it everywhere on the
closed triangle.  Thus the analytic integral equation may supply continuity,
while Palm disintegration only needs to supply the a.e. identity; no informal
"modify on a null set and glue" step remains. -/
lemma continuousOn_local_additivity_of_ae (f : ℝ → ℝ)
    (hf : ContinuousOn f (Icc (0 : ℝ) 1))
    (hae : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
      z ∈ localCauchyTriangle →
        f (z.1 + z.2) = f z.1 + f z.2) :
    ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      x + y ≤ 1 → f (x + y) = f x + f y := by
  let lhs : ℝ × ℝ → ℝ := fun z ↦ f (z.1 + z.2)
  let rhs : ℝ × ℝ → ℝ := fun z ↦ f z.1 + f z.2
  have hsumMaps : MapsTo (fun z : ℝ × ℝ ↦ z.1 + z.2)
      localCauchyTriangle (Icc (0 : ℝ) 1) := by
    intro z hz
    exact ⟨add_nonneg hz.1 hz.2.1, hz.2.2⟩
  have hfstMaps : MapsTo Prod.fst localCauchyTriangle (Icc (0 : ℝ) 1) := by
    intro z hz
    exact ⟨hz.1, (le_add_of_nonneg_right hz.2.1).trans hz.2.2⟩
  have hsndMaps : MapsTo Prod.snd localCauchyTriangle (Icc (0 : ℝ) 1) := by
    intro z hz
    exact ⟨hz.2.1, (le_add_of_nonneg_left hz.1).trans hz.2.2⟩
  have hlhs : ContinuousOn lhs localCauchyTriangle := by
    exact hf.comp (continuous_fst.add continuous_snd).continuousOn hsumMaps
  have hrhs : ContinuousOn rhs localCauchyTriangle := by
    exact (hf.comp continuous_fst.continuousOn hfstMaps).add
      (hf.comp continuous_snd.continuousOn hsndMaps)
  have haeRestrict : lhs =ᵐ[(volume.prod volume).restrict localCauchyTriangle] rhs := by
    apply (ae_restrict_iff' localCauchyTriangle_closed.measurableSet).2
    simpa only [lhs, rhs] using hae
  have heq : EqOn lhs rhs localCauchyTriangle :=
    Measure.eqOn_of_ae_eq haeRestrict hlhs hrhs
      localCauchyTriangle_subset_closure_interior
  intro x hx y hy hxy
  change lhs (x, y) = rhs (x, y)
  exact heq ⟨hx.1, hy.1, hxy⟩

end Erdos390.Full.PalmDisintegrationLogic
