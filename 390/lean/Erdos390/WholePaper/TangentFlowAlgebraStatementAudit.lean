import Erdos390.WholePaper.TangentFlowAlgebra

/-! # Expanded statement audit for exact tangent-flow algebra -/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

example {ι : Type*} (requests : Finset ι)
    (source target multiplier : ι → ℕ) (weight : ι → ℝ)
    (x : ℕ → ℝ) (A : Finset ℕ) (p : ℕ)
    (hsourceMem : ∀ e ∈ requests, source e * multiplier e ∈ A)
    (htargetMem : ∀ e ∈ requests, target e * multiplier e ∈ A)
    (hsourcePos : ∀ e ∈ requests, source e ≠ 0)
    (htargetPos : ∀ e ∈ requests, target e ≠ 0)
    (hmultiplierPos : ∀ e ∈ requests, multiplier e ≠ 0) :
    ∑ a ∈ A,
        (x a +
            ∑ e ∈ requests, weight e *
              ((if a = source e * multiplier e then (1 : ℝ) else 0) -
                (if a = target e * multiplier e then (1 : ℝ) else 0))) *
          (a.factorization p : ℝ) =
      (∑ a ∈ A, x a * (a.factorization p : ℝ)) +
        ∑ e ∈ requests, weight e *
          ((source e).factorization p - (target e).factorization p : ℝ) := by
  simpa only [tangentUpdate, tangentDelta, tangentPointMass] using
    tangentUpdate_valuation requests source target multiplier weight x A p
      hsourceMem htargetMem hsourcePos htargetPos hmultiplierPos

example {ι : Type*} (requests : Finset ι)
    (source target multiplier : ι → ℕ) (weight : ι → ℝ)
    (x : ℕ → ℝ) (A : Finset ℕ) (targetValuation : ℕ → ℝ)
    (hsourceMem : ∀ e ∈ requests, source e * multiplier e ∈ A)
    (htargetMem : ∀ e ∈ requests, target e * multiplier e ∈ A)
    (hsourcePos : ∀ e ∈ requests, source e ≠ 0)
    (htargetPos : ∀ e ∈ requests, target e ≠ 0)
    (hmultiplierPos : ∀ e ∈ requests, multiplier e ≠ 0)
    (hboundary : ∀ p : ℕ,
      ∑ e ∈ requests, weight e *
          ((source e).factorization p - (target e).factorization p : ℝ) =
        targetValuation p -
          ∑ a ∈ A, x a * (a.factorization p : ℝ)) :
    ∀ p : ℕ,
      ∑ a ∈ A,
          (x a +
              ∑ e ∈ requests, weight e *
                ((if a = source e * multiplier e then (1 : ℝ) else 0) -
                  (if a = target e * multiplier e then (1 : ℝ) else 0))) *
            (a.factorization p : ℝ) = targetValuation p := by
  simpa only [tangentUpdate, tangentDelta, tangentPointMass] using
    tangentUpdate_valuation_eq_target requests source target multiplier
      weight x A targetValuation hsourceMem htargetMem hsourcePos htargetPos
      hmultiplierPos hboundary

example {ι σ : Type*} [DecidableEq σ]
    (requests : Finset ι)
    (source target multiplier : ι → ℕ) (weight : ι → ℝ)
    (x : ℕ → ℝ) (A : Finset ℕ) (signature : ℕ → σ) (row : σ)
    (hsource : ∀ e ∈ requests, source e * multiplier e ∈ A)
    (htarget : ∀ e ∈ requests, target e * multiplier e ∈ A)
    (hsame : ∀ e ∈ requests,
      signature (source e * multiplier e) =
        signature (target e * multiplier e)) :
    ∑ a ∈ A.filter (fun a ↦ signature a = row),
        (x a +
          ∑ e ∈ requests, weight e *
            ((if a = source e * multiplier e then (1 : ℝ) else 0) -
              (if a = target e * multiplier e then (1 : ℝ) else 0))) =
      ∑ a ∈ A.filter (fun a ↦ signature a = row), x a := by
  simpa only [tangentUpdate, tangentDelta, tangentPointMass] using
    tangentUpdate_signatureRow requests source target multiplier weight x A
      signature row hsource htarget hsame

example {ι : Type*} (requests : Finset ι)
    (source target multiplier : ι → ℕ) (weight : ι → ℝ)
    (x : ℕ → ℝ) (A : Finset ℕ)
    (hsourceMem : ∀ e ∈ requests, source e * multiplier e ∈ A)
    (htargetMem : ∀ e ∈ requests, target e * multiplier e ∈ A)
    (hsourcePos : ∀ e ∈ requests, 0 < source e)
    (htargetPos : ∀ e ∈ requests, 0 < target e)
    (hmultiplierPos : ∀ e ∈ requests, 0 < multiplier e)
    (hlogBalance :
      ∑ e ∈ requests, weight e *
        (Real.log (source e : ℝ) - Real.log (target e : ℝ)) = 0) :
    ∑ a ∈ A,
        (x a +
            ∑ e ∈ requests, weight e *
              ((if a = source e * multiplier e then (1 : ℝ) else 0) -
                (if a = target e * multiplier e then (1 : ℝ) else 0))) *
          Real.log (a : ℝ) =
      ∑ a ∈ A, x a * Real.log (a : ℝ) := by
  simpa only [tangentUpdate, tangentDelta, tangentPointMass] using
    tangentUpdate_log requests source target multiplier weight x A
      hsourceMem htargetMem hsourcePos htargetPos hmultiplierPos hlogBalance

end

end Erdos390.WholePaper
