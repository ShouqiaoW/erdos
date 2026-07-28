import Erdos390.Full.PaperActualSquarefreeReference

/-!
# Direct finite assembly of the actual full projected inverse

The analytic prime-power work naturally exports a unit sharp-row estimate.
This file consumes that estimate directly, after the squarefree projected
operator has been inverted.  No reference law or Lemma 7.5 certificate is
carried as an additional hypothesis at this deterministic layer.
-/

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open PaperWeightedInverseExport

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- Stable inverse for the actual full-valuation projected operator from a
proved squarefree inverse and the literal full-vs-squarefree unit row. -/
theorem exists_actualFullProjectedEquiv_of_squarefree_of_unitSharpRows
    [Nonempty Head]
    (xi : B.ParamSpace)
    (squarefreeEquiv :
      SharpGaugeSpace B.partition.mass B.partition.center ≃L[ℝ]
        SharpGaugeSpace B.partition.mass B.partition.center)
    (hsquarefree : ∀ q, squarefreeEquiv q =
      B.actualSquarefreeProjectedCLM xi q)
    {C rpow : ℝ}
    (hC : 0 ≤ C) (hrpow : 0 ≤ rpow)
    (hinv : ∀ v, ‖squarefreeEquiv.symm v‖ ≤ C * ‖v‖)
    (hsmall : C * (2 * rpow) < 1)
    (hunit : ∀ q : Band → ℝ, (∀ j, |q j| ≤ 1) → ∀ i : Band,
      |PrimePowerSharpBandTransfer.fullSharpRow
          (B.actualValuationLaw xi) B.partition q i -
        SquarefreeSharpBandTransfer.squarefreeSharpRow
          (B.actualValuationLaw xi) B.partition q i| ≤ rpow) :
    ∃ actualEquiv :
      SharpGaugeSpace B.partition.mass B.partition.center ≃L[ℝ]
        SharpGaugeSpace B.partition.mass B.partition.center,
      (∀ q, actualEquiv q = B.actualFullProjectedCLM xi q) ∧
      ∀ v, ‖actualEquiv.symm v‖ ≤
        (C / (1 - C * (2 * rpow))) * ‖v‖ := by
  let A := B.actualSquarefreeProjectedCLM xi
  let Ainv : SharpGaugeSpace B.partition.mass B.partition.center →L[ℝ]
      SharpGaugeSpace B.partition.mass B.partition.center :=
    squarefreeEquiv.symm
  let E := B.actualFullProjectedCLM xi - A
  have hleft (q : SharpGaugeSpace
      B.partition.mass B.partition.center) : Ainv (A q) = q := by
    dsimp only [Ainv, A]
    rw [← hsquarefree q]
    exact squarefreeEquiv.symm_apply_apply q
  have hinv' (v : SharpGaugeSpace
      B.partition.mass B.partition.center) : ‖Ainv v‖ ≤ C * ‖v‖ :=
    hinv v
  have herror (q : SharpGaugeSpace
      B.partition.mass B.partition.center) :
      ‖E q‖ ≤ (2 * rpow) * ‖q‖ := by
    dsimp only [E, A]
    exact B.actualFullProjectedCLM_sub_squarefree_le_of_unitSharpRows
      xi hrpow hunit q
  let actualEquiv := StableInverse.perturbedEquiv
    A Ainv E C (2 * rpow) hC hsmall hleft hinv' herror
  refine ⟨actualEquiv, ?_, ?_⟩
  · intro q
    rw [StableInverse.perturbedEquiv_apply]
    dsimp only [actualEquiv, E]
    simp only [add_sub_cancel]
  · intro v
    exact StableInverse.perturbed_inverse_bound
      A Ainv E C (2 * rpow) hC hsmall hleft hinv' herror v

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
