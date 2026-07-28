import Erdos390.Full.PaperPrimePowerRemainderRate

/-!
# A uniform auxiliary prime for diagonal restoration

The diagonal probability is recovered from the two-local restoration by
giving each row prime a distinct auxiliary band prime with exponent zero.
Two fixed primes above the cutoff suffice once the moving band reaches them.
-/

open Filter

namespace Erdos390.Full.PaperPrimePowerAuxiliaryPrime

open ArithmeticModel HeadPattern

noncomputable section

/-- A modulus bound implies the weaker support bound which is actually used
to separate the prescribed head primes from the moving band.  This lemma is
kept only for backwards-compatible callers; the paper-facing route uses the
support bound directly, since a pattern containing every prime at most `W`
has modulus much larger than `W`. -/
theorem headPrime_le_cutoff_of_modulus_le
    (H : Pattern) {W : ℕ} (hHW : H.modulus ≤ W) :
    ∀ q ∈ H.primes, q ≤ W := by
  intro q hq
  have hqDiv : q ∣ H.modulus := by
    unfold Pattern.modulus
    exact Finset.dvd_prod_of_mem (fun r : ℕ => r) hq
  exact (Nat.le_of_dvd
    (Nat.pos_of_ne_zero H.modulus_ne_zero) hqDiv).trans hHW

/-- Every prime in the moving band is coprime to the head modulus as soon as
all primes occurring in the head pattern lie at or below the cutoff.  Unlike
`H.modulus ≤ W`, this is compatible with prescribing every prime `q ≤ W`. -/
theorem coprime_modulus_of_mem_primeBand_of_headSupport
    (H : Pattern) {n W p : ℕ}
    (hHeadLe : ∀ q ∈ H.primes, q ≤ W)
    (hpBand : p ∈ primeBand n W) : Nat.Coprime p H.modulus := by
  rw [Pattern.modulus, Nat.coprime_prod_right_iff]
  intro q hq
  have hp := prime_of_mem_primeBand hpBand
  have hqPrime := H.prime_mem q hq
  have hpGt : W < p := cutoff_lt_of_mem_primeBand hpBand
  have hpq : p ≠ q := by
    intro hpq
    subst q
    exact (Nat.not_lt_of_ge (hHeadLe p hq)) hpGt
  exact (Nat.coprime_primes hp hqPrime).mpr hpq

theorem coprime_modulus_of_mem_primeBand
    (H : Pattern) {n W p : ℕ} (hHW : H.modulus ≤ W)
    (hpBand : p ∈ primeBand n W) : Nat.Coprime p H.modulus := by
  exact coprime_modulus_of_mem_primeBand_of_headSupport H
    (headPrime_le_cutoff_of_modulus_le H hHW) hpBand

/-- Two fixed primes above `W`; the selected one is always different from
the current row prime. -/
theorem exists_eventually_auxiliaryPrime
    (W : ℕ) :
    ∃ q₀ q₁ : ℕ, ∃ aux : ℕ → ℕ,
      q₀.Prime ∧ q₁.Prime ∧ W < q₀ ∧ q₀ < q₁ ∧
      aux = (fun p ↦ if p = q₀ then q₁ else q₀) ∧
      ∀ᶠ n : ℕ in atTop,
        q₀ ∈ primeBand n W ∧ q₁ ∈ primeBand n W ∧
          ∀ p ∈ primeBand n W,
            aux p ∈ (primeBand n W).erase p := by
  obtain ⟨q₀, hWq₀, hq₀⟩ := Nat.exists_infinite_primes (W + 1)
  obtain ⟨q₁, hq₀q₁, hq₁⟩ := Nat.exists_infinite_primes (q₀ + 1)
  let aux : ℕ → ℕ := fun p ↦ if p = q₀ then q₁ else q₀
  have hWltq₀ : W < q₀ := by omega
  have hq₀ltq₁ : q₀ < q₁ := by omega
  have hyTop : Tendsto (fun n : ℕ ↦ y n) atTop atTop := by
    simpa [y] using
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 9)).comp
        tendsto_natCast_atTop_atTop)
  have hreach : ∀ᶠ n : ℕ in atTop, (q₁ : ℝ) ≤ y n :=
    hyTop.eventually (eventually_ge_atTop (q₁ : ℝ))
  refine ⟨q₀, q₁, aux, hq₀, hq₁, hWltq₀, hq₀ltq₁, rfl, ?_⟩
  filter_upwards [hreach] with n hqn
  have hq₁Y : q₁ ≤ yNat n := Nat.le_floor hqn
  have hq₀Y : q₀ ≤ yNat n := hq₀ltq₁.le.trans hq₁Y
  have hq₀Band : q₀ ∈ primeBand n W :=
    mem_primeBand.mpr ⟨hq₀, hWltq₀, hq₀Y⟩
  have hq₁Band : q₁ ∈ primeBand n W :=
    mem_primeBand.mpr ⟨hq₁, hWltq₀.trans hq₀ltq₁, hq₁Y⟩
  refine ⟨hq₀Band, hq₁Band, ?_⟩
  intro p hpBand
  by_cases hpq₀ : p = q₀
  · have hq₁p : q₁ ≠ p := by omega
    simpa only [aux, if_pos hpq₀] using
      (Finset.mem_erase.mpr ⟨hq₁p, hq₁Band⟩)
  · have hq₀p : q₀ ≠ p := by exact fun h ↦ hpq₀ h.symm
    simpa only [aux, if_neg hpq₀] using
      (Finset.mem_erase.mpr ⟨hq₀p, hq₀Band⟩)

end

end Erdos390.Full.PaperPrimePowerAuxiliaryPrime
