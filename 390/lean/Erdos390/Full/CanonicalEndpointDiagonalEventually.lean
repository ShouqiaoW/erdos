import Erdos390.Full.CanonicalEndpointRelativeCenterEventually
import Erdos390.Full.DiagonalPrimeQuadrature

/-!
# Canonical endpoint convergence of the diagonal multiplier

The normalized diagonal PNT estimate contains the actual output-cell mass
in its denominator.  This file proves that the denominator has the required
limit on every literal canonical cell: it diverges on the moving low cell
and tends to a positive constant on every positive cell.  Thus no
``mass is large'' hypothesis remains in the final diagonal statement.
-/

open Filter Topology

noncomputable section

namespace Erdos390.Full.RegularMeshPrimeCutoffs

open ArithmeticModel RegularRelativeMesh PrimeBandQuadrature
open DiagonalPrimeQuadrature DoubleKernelPrimeQuadrature
open KernelPrimeQuadrature

namespace Mesh

variable {delta eta : ℝ} (M : Mesh delta eta)

def endpointActualMass (n W : ℕ) (j : Fin (M.cellCount + 1)) : ℝ :=
  actualCellMass (fullCutoff M n W j.1)
    (fullCutoff M n W (j.1 + 1))

def endpointDiagonalError (n W : ℕ)
    (j : Fin (M.cellCount + 1)) : ℝ :=
  |normalizedDiagonalPrimeCell (y n)
      (fullCutoff M n W j.1) (fullCutoff M n W (j.1 + 1)) -
    normalizedDiagonalContinuumCell (y n)
      (fullCutoff M n W j.1) (fullCutoff M n W (j.1 + 1))|

theorem endpointActualMass_eq_fullReciprocalSum_sub
    (n W : ℕ) (j : Fin (M.cellCount + 1)) :
    endpointActualMass M n W j =
      PrimeSums.fullReciprocalSum (fullCutoff M n W (j.1 + 1)) -
        PrimeSums.fullReciprocalSum (fullCutoff M n W j.1) := by
  rfl

theorem endpointContinuumMass_eq_doubleKernelMass
    {n W : ℕ} (hn : 1 < n) (j : Fin (M.cellCount + 1))
    (hLowerTwo : 2 ≤ fullCutoff M n W j.1)
    (hMono : fullCutoff M n W j.1 ≤
      fullCutoff M n W (j.1 + 1)) :
    endpointContinuumMass M n W j =
      continuumCellMass (y n) (fullCutoff M n W j.1)
        (fullCutoff M n W (j.1 + 1)) := by
  have hy : 1 < y n := by
    have hlog : 0 < Real.log (y n) := by
      rw [Scale.log_y (Nat.zero_lt_of_lt hn)]
      exact mul_pos (by norm_num) (Real.log_pos (by exact_mod_cast hn))
    exact (Real.log_pos_iff (Scale.y_pos
      (Nat.zero_lt_of_lt hn)).le).mp hlog
  unfold endpointContinuumMass continuumCellMass
  have h := log_logCoordinate_sub hy hLowerTwo hMono
  simpa only [PrimeBandQuadrature.logCoordinate,
    realLogCoordinate] using h.symm

theorem tendsto_positive_endpointActualMass
    (hdelta : 0 < delta) (W : ℕ) (C : ℝ) (X : ℕ)
    (hMass : ∀ A Y : ℕ, X ≤ A → A ≤ Y →
      |PrimeSums.fullReciprocalSum Y - PrimeSums.fullReciprocalSum A -
        (Real.log (Real.log (Y : ℝ)) -
          Real.log (Real.log (A : ℝ)))| ≤
        5 * C / Real.log (A : ℝ) ^ 3)
    (k : Fin M.cellCount) :
    Tendsto (fun n : ℕ ↦
      endpointActualMass M n W (positiveBand M k)) atTop
      (nhds (Real.log (M.upper k) - Real.log (M.lower k))) := by
  have hCont := tendsto_positive_endpointContinuumMass M hdelta W k
  have hErr := tendsto_positive_endpointMassError_zero M hdelta C W k
  have hThreshold := eventually_threshold_le_nonlow_fullCutoff M hdelta W X
    (positiveBand M k) (by
      intro h
      have hv := congrArg Fin.val h
      simp only [positiveBand, lowBand, Fin.val_mk] at hv
      omega)
  have hSep := eventually_scaleSeparation M hdelta W
  have hDiff : Tendsto (fun n : ℕ ↦
      endpointActualMass M n W (positiveBand M k) -
        endpointContinuumMass M n W (positiveBand M k))
      atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hAbs : ∀ᶠ n : ℕ in atTop,
        |endpointActualMass M n W (positiveBand M k) -
          endpointContinuumMass M n W (positiveBand M k)| ≤
            endpointMassError M C n W (positiveBand M k) := by
      filter_upwards [eventually_gt_atTop 1, hThreshold, hSep] with
        n hn hX S
      have hmono := fullCutoff_monotone M hdelta hn
        (W_le_first_fullCutoff M S) (by omega : k.1 + 1 ≤ k.1 + 2)
      have hq := hMass (fullCutoff M n W (k.1 + 1))
        (fullCutoff M n W (k.1 + 2)) hX hmono
      simpa only [endpointActualMass, endpointContinuumMass,
        endpointMassError, positiveBand] using hq
    have hsqueeze := squeeze_zero'
      (Filter.Eventually.of_forall (fun n : ℕ => abs_nonneg
        (endpointActualMass M n W (positiveBand M k) -
          endpointContinuumMass M n W (positiveBand M k))))
      hAbs hErr
    simpa only [Real.norm_eq_abs] using hsqueeze
  have hsum := hDiff.add hCont
  simpa only [sub_add_cancel, zero_add] using hsum

theorem tendsto_low_endpointActualMass_atTop
    (hdelta : 0 < delta) {W X : ℕ} (hXW : X ≤ W)
    (C : ℝ)
    (hMass : ∀ A Y : ℕ, X ≤ A → A ≤ Y →
      |PrimeSums.fullReciprocalSum Y - PrimeSums.fullReciprocalSum A -
        (Real.log (Real.log (Y : ℝ)) -
          Real.log (Real.log (A : ℝ)))| ≤
        5 * C / Real.log (A : ℝ) ^ 3) :
    Tendsto (fun n : ℕ ↦ endpointActualMass M n W (lowBand M))
      atTop atTop := by
  have hCont := tendsto_low_endpointContinuumMass_atTop M hdelta W
  rw [tendsto_atTop]
  intro b
  let E₀ := 5 * C / Real.log (W : ℝ) ^ 3
  have hLarge := hCont.eventually (eventually_ge_atTop (b + E₀))
  have hSep := eventually_scaleSeparation M hdelta W
  filter_upwards [eventually_gt_atTop 1, hLarge, hSep] with n hn hlarge S
  have hmono := fullCutoff_monotone M hdelta hn
    (W_le_first_fullCutoff M S) (by omega : 0 ≤ 1)
  have hq := hMass W (fullCutoff M n W 1) hXW (by
    simpa only [fullCutoff_zero] using hmono)
  have hleft := (abs_le.mp hq).1
  have hLower :
      endpointContinuumMass M n W (lowBand M) - E₀ ≤
        endpointActualMass M n W (lowBand M) := by
    change -(5 * C / Real.log (W : ℝ) ^ 3) ≤
      endpointActualMass M n W (lowBand M) -
        endpointContinuumMass M n W (lowBand M) at hleft
    linarith
  linarith

/-- The actual canonical normalized diagonal converges uniformly over the
finite band set.  The PNT constants and cutoff threshold are chosen before
the requested accuracy and before `n`. -/
theorem exists_global_cutoff_eventually_canonical_diagonalError :
    ∃ W₀ : ℕ,
      ∀ {delta eta : ℝ} (M : Mesh delta eta), 0 < delta →
      ∀ W : ℕ, W₀ ≤ W → ∀ e : ℝ, 0 < e →
        ∀ᶠ n : ℕ in atTop,
          ∀ j : Fin (M.cellCount + 1), endpointDiagonalError M n W j ≤ e := by
  obtain ⟨Mdiag, hMdiag, Ddiag, hDdiag, Cdiag, hCdiag,
    Xdiag, hDiag⟩ := exists_uniform_normalizedDiagonalCell_error_bound
  obtain ⟨Cmass, hCmass, Xmass, hMass⟩ :=
    exists_fullReciprocalSum_interval_error_bound
  let W₀ := max 2 (max Xdiag Xmass)
  refine ⟨W₀, ?_⟩
  intro delta eta M hdelta W hW e he
  have hW2 : 2 ≤ W := (le_max_left 2 (max Xdiag Xmass)).trans hW
  have hXdiag : Xdiag ≤ W :=
    ((le_max_left Xdiag Xmass).trans
      (le_max_right 2 (max Xdiag Xmass))).trans hW
  have hXmass : Xmass ≤ W :=
    ((le_max_right Xdiag Xmass).trans
      (le_max_right 2 (max Xdiag Xmass))).trans hW
  have hLowActual := tendsto_low_endpointActualMass_atTop M hdelta
    hXmass Cmass hMass
  have hLowCont := tendsto_low_endpointContinuumMass_atTop M hdelta W
  have hLowBound : Tendsto (fun n : ℕ ↦
      (Ddiag / Real.log (W : ℝ) ^ 3) /
          endpointActualMass M n W (lowBand M) +
        (Mdiag * endpointContinuumMass M n W (lowBand M)) *
          (5 * Cdiag / Real.log (W : ℝ) ^ 3) /
          (endpointActualMass M n W (lowBand M) *
            |endpointContinuumMass M n W (lowBand M)|))
      atTop (nhds 0) := by
    have hFirstNum : Tendsto (fun _n : ℕ ↦
        Ddiag / Real.log (W : ℝ) ^ 3) atTop
        (nhds (Ddiag / Real.log (W : ℝ) ^ 3)) := tendsto_const_nhds
    have hFirst := hFirstNum.div_atTop hLowActual
    have hSecondNum : Tendsto (fun _n : ℕ ↦
        Mdiag * (5 * Cdiag / Real.log (W : ℝ) ^ 3)) atTop
        (nhds (Mdiag * (5 * Cdiag / Real.log (W : ℝ) ^ 3))) :=
      tendsto_const_nhds
    have hSecondSimple := hSecondNum.div_atTop hLowActual
    have hContPos := hLowCont.eventually (eventually_gt_atTop 0)
    have hSecond : Tendsto (fun n : ℕ ↦
        (Mdiag * endpointContinuumMass M n W (lowBand M)) *
          (5 * Cdiag / Real.log (W : ℝ) ^ 3) /
          (endpointActualMass M n W (lowBand M) *
            |endpointContinuumMass M n W (lowBand M)|))
        atTop (nhds 0) := by
      have hSimple : Tendsto (fun n : ℕ ↦
          (Mdiag * (5 * Cdiag / Real.log (W : ℝ) ^ 3)) /
            endpointActualMass M n W (lowBand M)) atTop (nhds 0) := by
        simpa using hSecondSimple
      apply hSimple.congr'
      filter_upwards [hContPos] with n hc
      rw [abs_of_pos hc]
      field_simp [ne_of_gt hc]
    simpa only [zero_add] using hFirst.add hSecond
  have hLowSmall := hLowBound.eventually (eventually_le_nhds he)
  have hPositiveSmall : ∀ᶠ n : ℕ in atTop,
      ∀ k : Fin M.cellCount,
      let A := fullCutoff M n W (k.1 + 1)
      let Y := fullCutoff M n W (k.1 + 2)
      ((Ddiag / Real.log (A : ℝ) ^ 3) /
          endpointActualMass M n W (positiveBand M k) +
        (Mdiag * endpointContinuumMass M n W (positiveBand M k)) *
          (5 * Cdiag / Real.log (A : ℝ) ^ 3) /
          (endpointActualMass M n W (positiveBand M k) *
            |endpointContinuumMass M n W (positiveBand M k)|)) ≤ e := by
    rw [Filter.eventually_all]
    intro k
    have hActual := tendsto_positive_endpointActualMass M hdelta W
      Cmass Xmass hMass k
    have hCont := tendsto_positive_endpointContinuumMass M hdelta W k
    have hAReal : Tendsto (fun n : ℕ ↦
        (fullCutoff M n W (k.1 + 1) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp
        (tendsto_general_positive_lowerCutoff_atTop M hdelta W k)
    have hLog := Real.tendsto_log_atTop.comp hAReal
    have hInvCube := (tendsto_inv_atTop_zero.comp hLog).pow 3
    let Hk := Real.log (M.upper k) - Real.log (M.lower k)
    have hHk : 0 < Hk := sub_pos.mpr
      (Real.strictMonoOn_log (M.lower_pos hdelta k)
        ((M.lower_pos hdelta k).trans (M.lower_lt_upper hdelta k))
        (M.lower_lt_upper hdelta k))
    have hActual0 : Hk ≠ 0 := ne_of_gt hHk
    have hCont0 : Hk ≠ 0 := ne_of_gt hHk
    have hFirst : Tendsto (fun n : ℕ ↦
        (Ddiag / Real.log (fullCutoff M n W (k.1 + 1) : ℝ) ^ 3) /
          endpointActualMass M n W (positiveBand M k))
        atTop (nhds 0) := by
      have hD : Tendsto (fun _n : ℕ ↦ Ddiag) atTop (nhds Ddiag) :=
        tendsto_const_nhds
      have hNum := hD.mul hInvCube
      have hDiv := hNum.div hActual hActual0
      have hDivZero : Tendsto (fun n : ℕ ↦
          (Ddiag *
            (Real.log (fullCutoff M n W (k.1 + 1) : ℝ))⁻¹ ^ 3) /
              endpointActualMass M n W (positiveBand M k))
          atTop (nhds 0) := by simpa using hDiv
      apply hDivZero.congr'
      filter_upwards with n
      rw [inv_pow]
      ring
    have hSecond : Tendsto (fun n : ℕ ↦
        (Mdiag * endpointContinuumMass M n W (positiveBand M k)) *
          (5 * Cdiag /
            Real.log (fullCutoff M n W (k.1 + 1) : ℝ) ^ 3) /
          (endpointActualMass M n W (positiveBand M k) *
            |endpointContinuumMass M n W (positiveBand M k)|))
        atTop (nhds 0) := by
      have hM : Tendsto (fun _n : ℕ ↦ Mdiag) atTop (nhds Mdiag) :=
        tendsto_const_nhds
      have hFiveC : Tendsto (fun _n : ℕ ↦ 5 * Cdiag) atTop
          (nhds (5 * Cdiag)) := tendsto_const_nhds
      have hNum := (hM.mul hCont).mul (hFiveC.mul hInvCube)
      have hAbs := hCont.abs
      have hDen := hActual.mul hAbs
      have hDen0 : Hk * |Hk| ≠ 0 :=
        mul_ne_zero hActual0 (abs_ne_zero.mpr hCont0)
      have hDiv := hNum.div hDen hDen0
      have hDivZero : Tendsto (fun n : ℕ ↦
          (Mdiag * endpointContinuumMass M n W (positiveBand M k) *
            (5 * Cdiag *
              (Real.log (fullCutoff M n W (k.1 + 1) : ℝ))⁻¹ ^ 3)) /
            (endpointActualMass M n W (positiveBand M k) *
              |endpointContinuumMass M n W (positiveBand M k)|))
          atTop (nhds 0) := by simpa using hDiv
      apply hDivZero.congr'
      filter_upwards with n
      rw [inv_pow]
      ring
    have hSum := hFirst.add hSecond
    exact hSum.eventually (eventually_le_nhds (by simpa using he))
  have hSep := eventually_scaleSeparation M hdelta W
  have hThreshold : ∀ᶠ n : ℕ in atTop,
      ∀ j : Fin (M.cellCount + 1), Xdiag ≤ fullCutoff M n W j.1 := by
    rw [Filter.eventually_all]
    intro j
    by_cases hj : j = lowBand M
    · subst j
      exact Filter.Eventually.of_forall (fun _n ↦ by
        simpa only [lowBand, fullCutoff_zero] using hXdiag)
    · exact eventually_threshold_le_nonlow_fullCutoff M hdelta W Xdiag j hj
  filter_upwards [eventually_gt_atTop 1, hSep, hLowSmall,
    hPositiveSmall, hThreshold] with n hn S hLow hPos hX
  intro j
  have hmono := fullCutoff_monotone M hdelta hn
    (W_le_first_fullCutoff M S) (Nat.le_succ j.1)
  have hY : (fullCutoff M n W (j.1 + 1) : ℝ) ≤ y n := by
    have hNat : fullCutoff M n W (j.1 + 1) ≤ yNat n := by
      rw [← fullCutoff_last M (Nat.zero_lt_of_lt hn)]
      exact fullCutoff_monotone M hdelta hn (W_le_first_fullCutoff M S)
        (by omega)
    exact (by exact_mod_cast hNat :
      (fullCutoff M n W (j.1 + 1) : ℝ) ≤ (yNat n : ℝ)) |>.trans
        (Nat.floor_le (Scale.y_pos (Nat.zero_lt_of_lt hn)).le)
  have hActualPos : 0 < endpointActualMass M n W j := by
    let P := canonicalPartition M hdelta hn (by omega : W ≠ 0) S
    let E := canonicalCertificate M hdelta hn (by omega : W ≠ 0) S
    have hp := P.data.mass_pos j
    have hEq : P.mass j = endpointActualMass M n W j := by
      rw [E.mass_eq_fullReciprocalSum_sub]
      rfl
    rw [← hEq]
    exact hp
  have hContPos : 0 < endpointContinuumMass M n W j := by
    obtain ⟨p, hpPrime, hpLower, hpUpper⟩ :=
      every_fullCutoff_cell_has_prime M (by omega : W ≠ 0) S j
    have hCutLt : fullCutoff M n W j.1 <
        fullCutoff M n W (j.1 + 1) := hpLower.trans_le hpUpper
    have hLowerTwo : 2 ≤ fullCutoff M n W j.1 :=
      hW2.trans (fullCutoff_monotone M hdelta hn
        (W_le_first_fullCutoff M S) (Nat.zero_le j.1))
    have hLowerPos : (0 : ℝ) < (fullCutoff M n W j.1 : ℝ) := by
      positivity
    have hUpperPos : (0 : ℝ) <
        (fullCutoff M n W (j.1 + 1) : ℝ) :=
      hLowerPos.trans (by exact_mod_cast hCutLt)
    have hLogLowerPos : 0 < Real.log (fullCutoff M n W j.1 : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < fullCutoff M n W j.1 by
        omega))
    have hLogUpperPos : 0 <
        Real.log (fullCutoff M n W (j.1 + 1) : ℝ) :=
      hLogLowerPos.trans (Real.strictMonoOn_log hLowerPos hUpperPos
        (by exact_mod_cast hCutLt))
    unfold endpointContinuumMass
    exact sub_pos.mpr (Real.strictMonoOn_log hLogLowerPos hLogUpperPos
      (Real.strictMonoOn_log hLowerPos hUpperPos
        (by exact_mod_cast hCutLt)))
  have hraw := hDiag (y n) (by
      have hlog : 0 < Real.log (y n) := by
        rw [Scale.log_y (Nat.zero_lt_of_lt hn)]
        exact mul_pos (by norm_num) (Real.log_pos (by exact_mod_cast hn))
      exact (Real.log_pos_iff (Scale.y_pos
        (Nat.zero_lt_of_lt hn)).le).mp hlog)
    (fullCutoff M n W j.1) (fullCutoff M n W (j.1 + 1))
    (hX j) hmono hY hActualPos
    (by
      rw [← endpointContinuumMass_eq_doubleKernelMass M hn j
        (hW2.trans (fullCutoff_monotone M hdelta hn
          (W_le_first_fullCutoff M S) (Nat.zero_le j.1))) hmono]
      exact ne_of_gt hContPos)
  unfold endpointDiagonalError
  apply hraw.trans
  rw [← endpointContinuumMass_eq_doubleKernelMass M hn j
      (hW2.trans (fullCutoff_monotone M hdelta hn
        (W_le_first_fullCutoff M S) (Nat.zero_le j.1))) hmono]
  change _ ≤ e
  refine Fin.cases ?_ (fun k ↦ ?_) j
  · simpa only [lowBand, Fin.val_mk, fullCutoff_zero] using hLow
  · simpa only [positiveBand] using hPos k

/-- Backwards-compatible fixed-mesh specialization of the global cutoff
statement. -/
theorem exists_cutoff_eventually_canonical_diagonalError
    (hdelta : 0 < delta) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ e : ℝ, 0 < e →
      ∀ᶠ n : ℕ in atTop,
        ∀ j : Fin (M.cellCount + 1), endpointDiagonalError M n W j ≤ e := by
  obtain ⟨W₀, hW₀⟩ :=
    exists_global_cutoff_eventually_canonical_diagonalError
  exact ⟨W₀, hW₀ M hdelta⟩

end Mesh
end Erdos390.Full.RegularMeshPrimeCutoffs
