import Erdos536.MainFromCubeApproximation
import Erdos536.CubeLawTensorBalance
import Erdos536.CanonicalCommonCubeLaw

/-!
# Reduction of arbitrary cube dimension to dimension one

The analytic construction only has to produce one-coordinate cube laws.
Independent tensor products add marginal errors and multiply balance
factors.  By splitting both requested errors at every induction step, this
gives the approximation property in every finite dimension.
-/

open Finset

namespace Erdos536

/-- The one-coordinate instance of the balanced-cube approximation
property. -/
def HasArbitrarilyGoodOneCubeApproximations : Prop :=
  ∀ (A : ℕ) (ε δ : ℝ), 0 < ε → 0 < δ →
    Nonempty (BalancedCubeApproximation 1 A ε δ)

private theorem canonicalCommonCubeLaw_empty_balanced
    {δ : ℝ} (hδ : 0 ≤ δ) :
    (canonicalCommonCubeLaw ∅
      (show IsPrimeSupport ∅ from by
        intro p hp
        simp at hp)).MultiplicativelyBalanced δ := by
  intro S hS ω τ
  have hSempty : S = ∅ := by
    simpa [canonicalCommonCubeLaw] using hS
  subst S
  have hωτ : ω = τ := Subsingleton.elim _ _
  subst τ
  have hnonneg :
      0 ≤
        (primeProduct
          (((canonicalCommonCubeLaw ∅
            (show IsPrimeSupport ∅ from by
              intro p hp
              simp at hp)).cube ∅).wordSupport ω) : ℝ) :=
    Nat.cast_nonneg _
  nlinarith

private theorem fin_append_restrict
    {H K : ℕ} (ω : Fin (H + K) → ZMod 3) :
    Fin.append
        (fun i : Fin H ↦ ω (Fin.castAdd K i))
        (fun j : Fin K ↦ ω (Fin.natAdd H j)) = ω := by
  funext i
  induction i using Fin.addCases with
  | left i => simp
  | right j => simp

private theorem support_disjoint_above_sup
    {R S : Finset ℕ} {A : ℕ}
    (hS : ∀ p ∈ S, max A (R.sup id) < p) :
    Disjoint R S := by
  rw [Finset.disjoint_left]
  intro p hpR hpS
  have hpSup : p ≤ R.sup id := Finset.le_sup (f := id) hpR
  have hpCut : p ≤ max A (R.sup id) :=
    hpSup.trans (le_max_right _ _)
  exact (not_lt_of_ge hpCut) (hS p hpS)

/-- One-coordinate approximations imply approximations in every finite
dimension. -/
theorem balancedCubeApproximations_of_one
    (hone : HasArbitrarilyGoodOneCubeApproximations) :
    HasArbitrarilyGoodBalancedCubeApproximations := by
  intro H
  induction H with
  | zero =>
      intro A ε δ hε hδ
      classical
      have hprime : IsPrimeSupport (∅ : Finset ℕ) := by
        intro p hp
        simp at hp
      refine ⟨{
        Sample := Finset ℕ
        sampleDecidableEq := (inferInstance : DecidableEq (Finset ℕ))
        primes := ∅
        primes_prime := hprime
        primes_above := by
          intro p hp
          simp at hp
        law := canonicalCommonCubeLaw ∅ hprime
        marginal_close := by
          intro ω
          rw [canonicalCommonCubeLaw_wordSupportDistance]
          exact hε.le
        balanced := canonicalCommonCubeLaw_empty_balanced hδ.le
      }⟩
  | succ H ih =>
      intro A ε δ hε hδ
      let η : ℝ := Real.sqrt (1 + δ) - 1
      have honeδ : (0 : ℝ) < 1 + δ := by linarith
      have hsqrt : (1 : ℝ) < Real.sqrt (1 + δ) := by
        simpa using Real.sqrt_lt_sqrt (show (0 : ℝ) ≤ 1 by norm_num)
          (show (1 : ℝ) < 1 + δ by linarith)
      have hη : 0 < η := sub_pos.mpr hsqrt
      obtain ⟨P⟩ := ih A (ε / 2) η (by positivity) hη
      letI : DecidableEq P.Sample := P.sampleDecidableEq
      let cutoff : ℕ := max A (P.primes.sup id)
      obtain ⟨Q⟩ := hone cutoff (ε / 2) η (by positivity) hη
      letI : DecidableEq Q.Sample := Q.sampleDecidableEq
      have hdisj : Disjoint P.primes Q.primes :=
        support_disjoint_above_sup Q.primes_above
      let T := P.law.tensor Q.law hdisj
      have hprime : IsPrimeSupport (P.primes ∪ Q.primes) := by
        intro p hp
        rcases Finset.mem_union.mp hp with hpP | hpQ
        · exact P.primes_prime p hpP
        · exact Q.primes_prime p hpQ
      refine ⟨{
        Sample := ↥P.law.samples × ↥Q.law.samples
        sampleDecidableEq := (inferInstance :
          DecidableEq (↥P.law.samples × ↥Q.law.samples))
        primes := P.primes ∪ Q.primes
        primes_prime := hprime
        primes_above := by
          intro p hp
          rcases Finset.mem_union.mp hp with hpP | hpQ
          · exact P.primes_above p hpP
          · exact (le_max_left A (P.primes.sup id)).trans_lt
              (Q.primes_above p hpQ)
        law := T
        marginal_close := by
          intro ω
          let ωP : Fin H → ZMod 3 :=
            fun i ↦ ω (Fin.castAdd 1 i)
          let ωQ : Fin 1 → ZMod 3 :=
            fun j ↦ ω (Fin.natAdd H j)
          have htensor :=
            P.law.tensor_wordSupportDistance_le Q.law
              P.primes_prime hdisj ωP ωQ
          rw [fin_append_restrict ω] at htensor
          exact htensor.trans (by
            have hP := P.marginal_close ωP
            have hQ := Q.marginal_close ωQ
            linarith)
        balanced := by
          have htensor :=
            P.law.tensor_multiplicativelyBalanced Q.law hdisj
              hη.le hη.le P.balanced Q.balanced
          have hηfactor :
              (1 + η) * (1 + η) - 1 = δ := by
            dsimp [η]
            calc
              (1 + (Real.sqrt (1 + δ) - 1)) *
                    (1 + (Real.sqrt (1 + δ) - 1)) - 1 =
                  (Real.sqrt (1 + δ)) ^ 2 - 1 := by ring
              _ = δ := by
                rw [Real.sq_sqrt honeδ.le]
                ring
          simpa [hηfactor] using htensor
      }⟩

/-- It therefore suffices to construct the one-coordinate laws in order to
deduce Erdős 536. -/
theorem mainTheorem_of_oneCubeApproximations
    (hone : HasArbitrarilyGoodOneCubeApproximations) :
    MainTheorem :=
  mainTheorem_of_balancedCubeApproximations
    (balancedCubeApproximations_of_one hone)

end Erdos536
