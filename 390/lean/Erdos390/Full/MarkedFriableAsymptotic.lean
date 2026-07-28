import Erdos390.Full.FriableAsymptotic
import Erdos390.Full.StructuredCells

open scoped BigOperators ArithmeticFunction.Moebius
open Filter Topology Asymptotics

namespace Erdos390.Full.MarkedFriableAsymptotic

open ArithmeticModel DickmanBasic Scale
open StructuredCells HeadPattern

theorem psi_eq_friableCount (X y : ℕ) :
    psi X y = FriableAsymptotic.friableCount X y := rfl

/-- The uniform Dickman estimate, including the zero endpoint. -/
theorem exists_uniform_psi_dickman_bound_all_endpoints :
    ∃ K : ℝ, 0 < K ∧ ∃ Y₀ : ℕ, ∀ {X y : ℕ},
      Y₀ ≤ y → Real.log (X : ℝ) ≤ 5 * Real.log (y : ℝ) →
      |(psi X y : ℝ) -
          (X : ℝ) * rho (FriableAsymptotic.dickmanU X y)| ≤
        K * (X : ℝ) / Real.log (y : ℝ) := by
  obtain ⟨K, hK, Y₀, hmain⟩ :=
    FriableAsymptotic.exists_uniform_friableCount_dickman_bound_all_faces
  refine ⟨K, hK, Y₀, ?_⟩
  intro X y hy hlog
  by_cases hX : X = 0
  · subst X
    simp [psi, FriableAsymptotic.dickmanU]
  · simpa only [psi_eq_friableCount] using
      hmain hy (Nat.pos_of_ne_zero hX) hlog

/-- Difference form for an actual smooth interval. -/
theorem exists_uniform_smoothInterval_dickman_bound :
    ∃ K : ℝ, 0 < K ∧ ∃ Y₀ : ℕ, ∀ {lo hi y : ℕ},
      Y₀ ≤ y → lo ≤ hi →
      Real.log (lo : ℝ) ≤ 5 * Real.log (y : ℝ) →
      Real.log (hi : ℝ) ≤ 5 * Real.log (y : ℝ) →
      |((smoothInterval lo hi y).card : ℝ) -
          ((hi : ℝ) * rho (FriableAsymptotic.dickmanU hi y) -
            (lo : ℝ) * rho (FriableAsymptotic.dickmanU lo y))| ≤
        K * ((hi : ℝ) + (lo : ℝ)) / Real.log (y : ℝ) := by
  obtain ⟨K, hK, Y₀, hpoint⟩ :=
    exists_uniform_psi_dickman_bound_all_endpoints
  refine ⟨K, hK, Y₀, ?_⟩
  intro lo hi y hy hlohi hloglo hloghi
  have hpsi : psi lo y ≤ psi hi y := by
    exact FriableAsymptotic.friableCount_mono_left hlohi
  have hhi := hpoint hy hloghi
  have hlo := hpoint hy hloglo
  rw [smoothInterval_card_eq_psi_sub hlohi]
  rw [Nat.cast_sub hpsi]
  calc
    _ = |(((psi hi y : ℝ) -
            (hi : ℝ) * rho (FriableAsymptotic.dickmanU hi y)) -
          ((psi lo y : ℝ) -
            (lo : ℝ) * rho (FriableAsymptotic.dickmanU lo y)))| := by ring_nf
    _ ≤ |(psi hi y : ℝ) -
            (hi : ℝ) * rho (FriableAsymptotic.dickmanU hi y)| +
          |(psi lo y : ℝ) -
            (lo : ℝ) * rho (FriableAsymptotic.dickmanU lo y)| := by
      have h := abs_sub_le
        ((psi hi y : ℝ) - (hi : ℝ) *
          rho (FriableAsymptotic.dickmanU hi y)) 0
        ((psi lo y : ℝ) - (lo : ℝ) *
          rho (FriableAsymptotic.dickmanU lo y))
      simpa only [sub_zero, zero_sub, abs_neg] using h
    _ ≤ K * (hi : ℝ) / Real.log (y : ℝ) +
          K * (lo : ℝ) / Real.log (y : ℝ) := add_le_add hhi hlo
    _ = K * ((hi : ℝ) + (lo : ℝ)) / Real.log (y : ℝ) := by ring

end Erdos390.Full.MarkedFriableAsymptotic
