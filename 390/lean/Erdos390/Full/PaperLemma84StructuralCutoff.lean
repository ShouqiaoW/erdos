import Erdos390.Full.PaperCanonicalPrimeAnchorEventually
import Erdos390.Full.PaperCanonicalPrimeRowResidualEventually
import Erdos390.Full.PaperCanonicalSlowKappa
import Erdos390.Full.PaperActualSquarefreeSlowLower
import Erdos390.Full.FixedFiniteMixtureFullUniform
import Erdos390.Full.PoissonDickmanKernelBounds

/-!
# Structural cutoff for the arithmetic quotient gap

The constants and cutoff in this file precede the mesh, the finite head
type, the exact head patterns, and every later tilt box.  Only vanishing
remainders will be selected after those data in the eventual theorem.
-/

open Filter Topology

namespace Erdos390.Full.PaperLemma84StructuralCutoff

noncomputable section

open ArithmeticModel
open PaperCanonicalSlowKappa
open PaperSquarefreeSlowQuadraticLower
open PaperBridgeFit.BridgeData
open PrimeSquarefreeDirichletGeometry
open FiniteAnchoredDirichletQuadratic

/-- The anchor mass is at least `1/8`, so the fixed-kappa Dirichlet main
coefficient is at least `canonicalSlowKappa / 16`. -/
def quotientMain : ℝ := canonicalSlowKappa / 16

/-- A small structural part of the row budget, fixed before the cutoff. -/
def quotientRowTarget : ℝ := quotientMain / 16

/-- The final uniform quotient constant after all perturbations are
absorbed. -/
def quotientKappa : ℝ := quotientMain / 2

theorem quotientMain_pos : 0 < quotientMain := by
  exact div_pos canonicalSlowKappa_pos (by norm_num)

theorem quotientRowTarget_pos : 0 < quotientRowTarget := by
  exact div_pos quotientMain_pos (by norm_num)

theorem quotientKappa_pos : 0 < quotientKappa := by
  exact div_pos quotientMain_pos (by norm_num)

/-- All non-vanishing arithmetic losses can be made small by one cutoff
chosen before the mesh and the head-pattern family. -/
theorem exists_structural_cutoff :
    ∃ CKernel : ℝ, 0 ≤ CKernel ∧
      (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
        |ConditionedPoissonLimit.covarianceKernel s t| ≤ CKernel * t) ∧
      ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
        2 ≤ W ∧
        RegularMeshPrimeCutoffs.Mesh.canonicalPrimeAnchorCutoff ≤ W ∧
        (∀ᶠ n : ℕ in atTop, ∀ p : PrimeIndex n W,
          |rowResidual (primeWeight n) (primeDiagonal n) (primeKernel n) p| ≤
            quotientRowTarget * tPrime n p.1) ∧
        quotientRowTarget +
            signedSecondConstant 0 CKernel * (1 / (W : ℝ)) +
            FixedFiniteMixtureFullUniform.boxIndependentPrimePowerConstant *
              (1 / (W : ℝ)) <
          quotientMain / 4 := by
  obtain ⟨CKernel, hCKernel, hKernel⟩ :=
    PoissonDickmanKernelBounds.exists_covarianceKernel_abs_le_second
  obtain ⟨Wrow, hrow⟩ :=
    PaperCanonicalPrimeRowResidualEventually.exists_cutoff_eventually_primeRowResidual_le
      quotientRowTarget_pos
  let Cpow : ℝ :=
    FixedFiniteMixtureFullUniform.boxIndependentPrimePowerConstant
  let tailConstant : ℝ := signedSecondConstant 0 CKernel + Cpow
  have hInv : Tendsto (fun W : ℕ ↦ 1 / (W : ℝ)) atTop (nhds 0) := by
    have hcast : Tendsto (fun W : ℕ ↦ (W : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop
    simpa only [one_div] using tendsto_inv_atTop_zero.comp hcast
  have htail : Tendsto
      (fun W : ℕ ↦ tailConstant * (1 / (W : ℝ)))
      atTop (nhds 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hInv
  have hsmall : ∀ᶠ W : ℕ in atTop,
      tailConstant * (1 / (W : ℝ)) < quotientMain / 16 :=
    htail.eventually (eventually_lt_nhds
      (div_pos quotientMain_pos (by norm_num)))
  obtain ⟨Wtail, hWtail⟩ := eventually_atTop.1 hsmall
  let W₀ := max 2
    (max RegularMeshPrimeCutoffs.Mesh.canonicalPrimeAnchorCutoff
      (max Wrow Wtail))
  refine ⟨CKernel, hCKernel, hKernel, W₀, ?_⟩
  intro W hW
  have htwo : 2 ≤ W := (le_max_left 2 _).trans hW
  have hanchor :
      RegularMeshPrimeCutoffs.Mesh.canonicalPrimeAnchorCutoff ≤ W :=
    ((le_max_left _ (max Wrow Wtail)).trans (le_max_right 2 _)).trans hW
  have hrowW : Wrow ≤ W :=
    ((le_max_left Wrow Wtail).trans
      (le_max_right _ (max Wrow Wtail))).trans (le_max_right 2 _ |>.trans hW)
  have htailW : Wtail ≤ W :=
    ((le_max_right Wrow Wtail).trans
      (le_max_right _ (max Wrow Wtail))).trans (le_max_right 2 _ |>.trans hW)
  have htailSmall := hWtail W htailW
  refine ⟨htwo, hanchor, hrow W hrowW, ?_⟩
  have hid :
      signedSecondConstant 0 CKernel * (1 / (W : ℝ)) +
          Cpow * (1 / (W : ℝ)) =
        tailConstant * (1 / (W : ℝ)) := by
    dsimp only [tailConstant]
    ring
  change quotientRowTarget +
      signedSecondConstant 0 CKernel * (1 / (W : ℝ)) +
        Cpow * (1 / (W : ℝ)) < quotientMain / 4
  rw [show quotientRowTarget +
        signedSecondConstant 0 CKernel * (1 / (W : ℝ)) +
          Cpow * (1 / (W : ℝ)) =
      quotientRowTarget + tailConstant * (1 / (W : ℝ)) by
        rw [← hid]
        ring]
  dsimp only [quotientRowTarget]
  linarith [quotientMain_pos]

end
end Erdos390.Full.PaperLemma84StructuralCutoff
