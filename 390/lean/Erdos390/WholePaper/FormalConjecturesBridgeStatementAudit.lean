import Erdos390.WholePaper.FormalConjecturesBridge

/-!
# Statement audit: Formal Conjectures bridge for Erdős 390

The final examples intentionally duplicate the theorem bodies in
`FormalConjectures/ErdosProblems/390.lean`, replacing only its root
`Erdos390.f` by the collision-free literal copy `formalF`.
-/

open scoped Nat BigOperators
open Filter Asymptotics Real

namespace Erdos390.WholePaper.FormalConjecturesBridge

noncomputable section

#check FCAdmissible
#check formalF
#check fcAdmissible_to_isAdmissibleEndpoint
#check isAdmissibleEndpoint_to_exists_fcAdmissible
#check formalF_eq_wholePaper_f
#check eventually_formalF_eq_wholePaper_f
#check wholePaper_isEquivalent_fixedC0_of_mainAsymptotic
#check formalF_isEquivalent_fixedC0_of_mainAsymptotic
#check formalF_isEquivalent_fixedC0
#check formalF_theta
#check formalF_rhs
#check theta_of_eventuallyEq_formalF
#check rhs_of_eventuallyEq_formalF

/-! ## Literal fixed-coefficient corollary -/

example :
    (fun n : ℕ => (formalF n : ℝ) - 2 * (n : ℝ)) ~[atTop]
      (fun n : ℕ =>
        Erdos390.WholePaper.C0 * (n : ℝ) / Real.log (n : ℝ)) :=
  formalF_isEquivalent_fixedC0

/-! ## Literal upstream theta statement -/

example :
    (fun n => formalF n - 2 * n : ℕ → ℝ) =Θ[atTop]
      (fun n => n / log (n : ℝ)) :=
  formalF_theta

/-! ## Literal upstream open-problem right-hand side -/

example :
    ∃ c,
      (fun n => formalF n - 2 * n : ℕ → ℝ) ~[atTop]
        (fun n => c * n / log (n : ℝ)) :=
  formalF_rhs

/-! ## Dependency-free downstream adapter contract -/

example {upstreamF : ℕ → ℕ} (h : ∀ n, upstreamF n = formalF n) :
    (fun n => upstreamF n - 2 * n : ℕ → ℝ) =Θ[atTop]
      (fun n => n / log (n : ℝ)) :=
  theta_of_eventuallyEq_formalF (Eventually.of_forall h)

example {upstreamF : ℕ → ℕ} (h : ∀ n, upstreamF n = formalF n) :
    ∃ c,
      (fun n => upstreamF n - 2 * n : ℕ → ℝ) ~[atTop]
        (fun n => c * n / log (n : ℝ)) :=
  rhs_of_eventuallyEq_formalF (Eventually.of_forall h)

end

end Erdos390.WholePaper.FormalConjecturesBridge
