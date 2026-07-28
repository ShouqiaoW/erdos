import Erdos390.Full.FiniteProbabilityMixture
import Erdos390.Full.FiniteTiltTV

/-!
# Exponential tilts of finite tagged mixtures

A global exponential tilt of a finite mixture is not obtained by retaining
the old cell weights.  The exact new weights contain the cell partition
functions.  This file proves that identity before any covariance is formed,
so common-profile estimates can safely be averaged across cells.
-/

open scoped BigOperators

namespace Erdos390.Full
namespace FiniteProbability

noncomputable section

variable {Cell : Type*} [Fintype Cell]
  {Omega : Cell → Type*} [∀ c, Fintype (Omega c)]

/-- Score restricted to one tagged component. -/
def sigmaCellScore (S : Sigma Omega → ℝ) (c : Cell) : Omega c → ℝ :=
  fun x => S ⟨c, x⟩

/-- The partition function of the global tagged law is the convex sum of
the component partition functions. -/
theorem sigmaMixture_expPartition
    (weight : FiniteProbability Cell)
    (mu : ∀ c, FiniteProbability (Omega c))
    (S : Sigma Omega → ℝ) :
    (sigmaMixture weight mu).expPartition S =
      ∑ c, weight.mass c * (mu c).expPartition (sigmaCellScore S c) := by
  rw [expPartition, sigmaMixture_expect]
  rfl

/-- Exact cell weights after globally tilting a tagged mixture. -/
def tiltedSigmaWeight
    (weight : FiniteProbability Cell)
    (mu : ∀ c, FiniteProbability (Omega c))
    (S : Sigma Omega → ℝ) : FiniteProbability Cell where
  mass c := weight.mass c *
    (mu c).expPartition (sigmaCellScore S c) /
      (sigmaMixture weight mu).expPartition S
  mass_nonneg c := div_nonneg
    (mul_nonneg (weight.mass_nonneg c)
      ((mu c).expPartition_pos (sigmaCellScore S c)).le)
    ((sigmaMixture weight mu).expPartition_pos S).le
  mass_sum := by
    rw [← Finset.sum_div, ← sigmaMixture_expPartition]
    exact div_self (ne_of_gt ((sigmaMixture weight mu).expPartition_pos S))

theorem tiltedSigmaWeight_mass
    (weight : FiniteProbability Cell)
    (mu : ∀ c, FiniteProbability (Omega c))
    (S : Sigma Omega → ℝ) (c : Cell) :
    (tiltedSigmaWeight weight mu S).mass c =
      weight.mass c * (mu c).expPartition (sigmaCellScore S c) /
        (sigmaMixture weight mu).expPartition S := rfl

/-- Pointwise exact factorization of the globally tilted density into the
new cell weight and the componentwise tilted density. -/
theorem exponentialTilt_sigmaMixture_mass
    (weight : FiniteProbability Cell)
    (mu : ∀ c, FiniteProbability (Omega c))
    (S : Sigma Omega → ℝ) (x : Sigma Omega) :
    ((sigmaMixture weight mu).exponentialTilt S).mass x =
      (sigmaMixture (tiltedSigmaWeight weight mu S)
        (fun c => (mu c).exponentialTilt (sigmaCellScore S c))).mass x := by
  rcases x with ⟨c, x⟩
  let Zc := (mu c).expPartition (sigmaCellScore S c)
  let Z := (sigmaMixture weight mu).expPartition S
  have hcellZ : Zc ≠ 0 :=
    ne_of_gt ((mu c).expPartition_pos (sigmaCellScore S c))
  have hglobalZ : Z ≠ 0 :=
    ne_of_gt ((sigmaMixture weight mu).expPartition_pos S)
  change weight.mass c * (mu c).mass x * Real.exp (S ⟨c, x⟩) / Z =
    (weight.mass c * Zc / Z) *
      ((mu c).mass x * Real.exp (S ⟨c, x⟩) / Zc)
  field_simp [hcellZ, hglobalZ]

private theorem finiteProbability_ext
    {Alpha : Type*} [Fintype Alpha]
    {mu nu : FiniteProbability Alpha} (h : mu.mass = nu.mass) : mu = nu := by
  cases mu with
  | mk massMu nonnegMu sumMu =>
    cases nu with
    | mk massNu nonnegNu sumNu =>
      dsimp only at h
      subst massNu
      rfl

/-- Equality of the two finite probability laws, not merely equality of
their expectations. -/
theorem exponentialTilt_sigmaMixture
    (weight : FiniteProbability Cell)
    (mu : ∀ c, FiniteProbability (Omega c))
    (S : Sigma Omega → ℝ) :
    (sigmaMixture weight mu).exponentialTilt S =
      sigmaMixture (tiltedSigmaWeight weight mu S)
        (fun c => (mu c).exponentialTilt (sigmaCellScore S c)) := by
  apply finiteProbability_ext
  funext x
  exact exponentialTilt_sigmaMixture_mass weight mu S x

/-- A common componentwise expectation profile survives the global tilt,
with the same error and with the correctly reweighted cell law. -/
theorem abs_exponentialTilt_sigmaMixture_expect_sub_common_le
    (weight : FiniteProbability Cell)
    (mu : ∀ c, FiniteProbability (Omega c))
    (S : Sigma Omega → ℝ) (F : Sigma Omega → ℝ)
    (main error : ℝ)
    (hcell : ∀ c,
      |((mu c).exponentialTilt (sigmaCellScore S c)).expect
          (fun x => F ⟨c, x⟩) - main| ≤ error) :
    |((sigmaMixture weight mu).exponentialTilt S).expect F - main| ≤
      error := by
  rw [exponentialTilt_sigmaMixture]
  exact abs_sigmaMixture_expect_sub_common_le
    (tiltedSigmaWeight weight mu S)
    (fun c => (mu c).exponentialTilt (sigmaCellScore S c))
    F main error hcell

/-- Likewise, a common componentwise upper expectation bound survives the
global tilt. -/
theorem exponentialTilt_sigmaMixture_expect_le_common
    (weight : FiniteProbability Cell)
    (mu : ∀ c, FiniteProbability (Omega c))
    (S : Sigma Omega → ℝ) (F : Sigma Omega → ℝ) (upper : ℝ)
    (hcell : ∀ c,
      ((mu c).exponentialTilt (sigmaCellScore S c)).expect
        (fun x => F ⟨c, x⟩) ≤ upper) :
    ((sigmaMixture weight mu).exponentialTilt S).expect F ≤ upper := by
  rw [exponentialTilt_sigmaMixture]
  exact sigmaMixture_expect_le_common
    (tiltedSigmaWeight weight mu S)
    (fun c => (mu c).exponentialTilt (sigmaCellScore S c))
    F upper hcell

end

end FiniteProbability
end Erdos390.Full
