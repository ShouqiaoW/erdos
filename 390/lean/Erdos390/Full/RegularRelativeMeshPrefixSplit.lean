import Erdos390.Full.RegularRelativeMeshInteriorAnchors

/-!
# Prefix split at a fixed logarithmic threshold

The moving low cell and all positive cells before the first ideal endpoint
crossing `tau` form the low block.  The remaining positive cells form the
high block.  The construction is purely ideal-mesh geometry and therefore
does not depend on the later arithmetic cutoff or ambient integer.
-/

namespace Erdos390.Full.RegularRelativeMesh

noncomputable section

namespace Mesh

variable {delta eta : ℝ} (M : Mesh delta eta)

def prefixIndex (tau : ℝ) (htau : tau ≤ 1) : ℕ :=
  M.firstEndpointAtLeast tau htau

abbrev prefixLow (tau : ℝ) (htau : tau ≤ 1) : Type :=
  Fin (M.prefixIndex tau htau + 1)

abbrev prefixHigh (tau : ℝ) (htau : tau ≤ 1) : Type :=
  Fin (M.cellCount - M.prefixIndex tau htau)

/-- The exact low-prefix/high-suffix reindexing of the full band set. -/
def prefixSplitEquiv (tau : ℝ) (htau : tau ≤ 1) :
    Sum (M.prefixLow tau htau) (M.prefixHigh tau htau) ≃
      Fin (M.cellCount + 1) :=
  finSumFinEquiv.trans (finCongr (by
    have hj := M.firstEndpointAtLeast_le_cellCount tau htau
    dsimp only [prefixLow, prefixHigh, prefixIndex]
    omega))

@[simp] theorem prefixSplitEquiv_inl_val
    (tau : ℝ) (htau : tau ≤ 1) (l : M.prefixLow tau htau) :
    (M.prefixSplitEquiv tau htau (.inl l)).1 = l.1 := by
  rfl

@[simp] theorem prefixSplitEquiv_inr_val
    (tau : ℝ) (htau : tau ≤ 1) (k : M.prefixHigh tau htau) :
    (M.prefixSplitEquiv tau htau (.inr k)).1 =
      M.prefixIndex tau htau + 1 + k.1 := by
  rfl

theorem width_lt_ratio (hdelta : 0 < delta) (k : Fin M.cellCount) :
    M.width k < M.ratio := by
  rw [M.width_eq_ratio_mul_lower]
  have hlowerOne : M.lower k < 1 :=
    (M.lower_lt_upper hdelta k).trans_le (M.upper_le_one hdelta k)
  nlinarith [M.ratio_pos]

theorem prefix_endpoint_lt_tau_add_ratio
    (hdelta : 0 < delta) {tau : ℝ} (htau : tau ≤ 1)
    (hdeltatau : delta < tau) :
    M.endpoint (M.prefixIndex tau htau) < tau + M.ratio := by
  exact M.firstEndpointAtLeast_endpoint_lt_add tau M.ratio htau
    hdeltatau (M.width_lt_ratio hdelta)

theorem prefix_endpoint_ge_tau (tau : ℝ) (htau : tau ≤ 1) :
    tau ≤ M.endpoint (M.prefixIndex tau htau) :=
  M.firstEndpointAtLeast_spec tau htau

/-- A small relative ratio ensures a nonempty high suffix. -/
theorem prefixIndex_lt_cellCount
    (hdelta : 0 < delta) {tau : ℝ} (htau : tau ≤ 1)
    (htauSmall : tau + M.ratio < 1) :
    M.prefixIndex tau htau < M.cellCount := by
  let last : Fin M.cellCount :=
    ⟨M.cellCount - 1, Nat.sub_lt M.cellCount_pos (by omega)⟩
  have hlastUpper : M.upper last = 1 := by
    dsimp only [last, upper]
    rw [Nat.sub_add_cancel M.cellCount_pos]
    exact M.endpoint_cellCount
  have hlastLower : tau < M.lower last := by
    have hwidth := M.width_lt_ratio hdelta last
    unfold width at hwidth
    rw [hlastUpper] at hwidth
    linarith
  have hWitness : tau ≤ M.endpoint (M.cellCount - 1) := by
    simpa only [last, lower] using hlastLower.le
  have hle : M.prefixIndex tau htau ≤ M.cellCount - 1 := by
    exact Nat.find_min' (M.exists_endpoint_ge tau htau) hWitness
  exact hle.trans_lt (Nat.sub_lt M.cellCount_pos (by omega))

instance prefixHigh_nonempty
    (hdelta : 0 < delta) {tau : ℝ} (htau : tau ≤ 1)
    (htauSmall : tau + M.ratio < 1) :
    Nonempty (M.prefixHigh tau htau) := by
  have hj := M.prefixIndex_lt_cellCount hdelta htau htauSmall
  exact Fin.pos_iff_nonempty.mp (Nat.sub_pos_of_lt hj)

/-- Every high suffix cell starts at or above the crossing threshold. -/
theorem lower_prefixSplitEquiv_inr_ge
    (hdelta : 0 < delta) {tau : ℝ} (htau : tau ≤ 1)
    (k : M.prefixHigh tau htau) :
    tau ≤ M.lower
      ⟨M.prefixIndex tau htau + k.1,
        by
          have hj := M.firstEndpointAtLeast_le_cellCount tau htau
          have hk := k.2
          dsimp only [prefixHigh, prefixIndex] at hk
          dsimp only [prefixIndex]
          omega⟩ := by
  have hspec := M.prefix_endpoint_ge_tau tau htau
  have hmono := (M.strictMono_endpoint hdelta).monotone
    (show M.prefixIndex tau htau ≤ M.prefixIndex tau htau + k.1 by omega)
  exact hspec.trans (by simpa only [lower] using hmono)

/-- Every positive cell placed in the low prefix ends no later than the
crossing endpoint. -/
theorem upper_le_prefix_endpoint_of_band_mem_low
    (hdelta : 0 < delta) {tau : ℝ} (htau : tau ≤ 1)
    (l : M.prefixLow tau htau) (hl : 0 < l.1) :
    let k : Fin M.cellCount :=
      ⟨l.1 - 1, by
        have hj := M.firstEndpointAtLeast_le_cellCount tau htau
        have hlv := l.2
        dsimp only [prefixLow, prefixIndex] at hlv
        omega⟩
    M.upper k ≤ M.endpoint (M.prefixIndex tau htau) := by
  dsimp only
  have hlv := l.2
  dsimp only [prefixLow, prefixIndex] at hlv
  unfold upper
  rw [show l.1 - 1 + 1 = l.1 by omega]
  exact (M.strictMono_endpoint hdelta).monotone (by omega)

/-- Every ideal anchor cell lying above `tau` belongs to the high suffix. -/
theorem prefixIndex_le_of_tau_lt_lower
    {tau : ℝ} (htau : tau ≤ 1)
    {k : Fin M.cellCount} (hk : tau < M.lower k) :
    M.prefixIndex tau htau ≤ k.1 := by
  by_contra hnot
  have hlt : k.1 < M.prefixIndex tau htau := by omega
  have hbelow := M.endpoint_lt_of_lt_firstEndpointAtLeast tau htau hlt
  exact (not_lt_of_ge hk.le) (by simpa only [lower] using hbelow)

end Mesh
end
end Erdos390.Full.RegularRelativeMesh
