import Erdos390.Full.RegularRelativeMeshPrefixSplit
import Erdos390.Full.CanonicalEndpointMultiAnchorIntervalMesh
import Erdos390.Full.CanonicalEndpointMeshGeometryEventually
import Erdos390.Full.ContinuumIntervalCenterBounds
import Erdos390.Full.ContinuumManyLowHighGeometry

/-!
# Canonical endpoint geometry for the moving prefix split

One literal boundary separates the low prefix from the high suffix.  Its
coordinate converges to the corresponding ideal endpoint.  Consequently,
ordinary centre and length estimates do not divide by the moving low-cell
centre and are uniform in the number of cells.
-/

open scoped BigOperators
open Filter

noncomputable section

namespace Erdos390.Full.RegularMeshPrimeCutoffs

open ArithmeticModel RegularRelativeMesh KernelPrimeQuadrature
  DoubleKernelPrimeQuadrature
  ContinuumCellGraph

namespace Mesh

variable {delta eta : ℝ} (M : Mesh delta eta)

def canonicalPrefixBoundary (n W : ℕ) (tau : ℝ) (htau : tau ≤ 1) : ℝ :=
  actualCutoffCoordinate M n W (M.prefixIndex tau htau + 1)

theorem tendsto_canonicalPrefixBoundary
    (hdelta : 0 < delta) (W : ℕ) (tau : ℝ) (htau : tau ≤ 1) :
    Tendsto (fun n : ℕ ↦ canonicalPrefixBoundary M n W tau htau)
      atTop (nhds (M.endpoint (M.prefixIndex tau htau))) := by
  simpa only [canonicalPrefixBoundary, actualCutoffCoordinate,
    fullCutoff_succ, RegularRelativeMesh.Mesh.prefixIndex] using
      tendsto_floor_scalePoint_coordinate
        (M.endpoint_pos hdelta (M.firstEndpointAtLeast tau htau))

/-- If the ideal mesh scale is small relative to `tau`, the actual prefix
boundary eventually stays between `tau/2` and `2*tau`. -/
theorem eventually_canonicalPrefixBoundary_between
    (hdelta : 0 < delta) {tau : ℝ} (htau : tau ≤ 1)
    (hdeltatau : delta < tau)
    (hratio : M.ratio ≤ tau / 2) (W : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      tau / 2 ≤ canonicalPrefixBoundary M n W tau htau ∧
        canonicalPrefixBoundary M n W tau htau ≤ 2 * tau := by
  let a := M.endpoint (M.prefixIndex tau htau)
  have haLower : tau / 2 < a := by
    have hspec := M.prefix_endpoint_ge_tau tau htau
    dsimp only [a]
    linarith
  have haUpper : a < 2 * tau := by
    have hcross := M.prefix_endpoint_lt_tau_add_ratio hdelta htau hdeltatau
    dsimp only [a]
    linarith
  have hlim := tendsto_canonicalPrefixBoundary M hdelta W tau htau
  have hlower := hlim.eventually (eventually_ge_nhds haLower)
  have hupper := hlim.eventually (eventually_le_nhds haUpper)
  filter_upwards [hlower, hupper] with n hnLower hnUpper
  exact ⟨hnLower, hnUpper⟩

section LiteralGeometry

variable {n W : ℕ} (hdelta : 0 < delta) (hn : 1 < n)
  (hW : W ≠ 0) (hWTwo : 2 ≤ W) (S : ScaleSeparation M n W)
  {tau epsilon : ℝ} (htau : tau ≤ 1)
  (anchors : Finset (Fin M.cellCount)) (hAnchors : anchors.Nonempty)
  (hIdealAnchorLower : ∀ k ∈ anchors, tau < M.lower k)
  (hInteriorLower : ∀ k ∈ anchors, epsilon ≤
    realLogCoordinate (y n)
      ((canonicalCertificate M hdelta hn hW S).lower
        (positiveBand M k) : ℝ))
  (hInteriorUpper : ∀ k ∈ anchors,
    realLogCoordinate (y n)
      ((canonicalCertificate M hdelta hn hW S).upper
        (positiveBand M k) : ℝ) ≤ 1 - epsilon)

theorem canonicalPrefix_low_center_le_boundary
    (l : M.prefixLow tau htau) :
    let IM := canonicalIntervalMeshOfAnchors M hdelta hn hW hWTwo S epsilon
      anchors hAnchors hInteriorLower hInteriorUpper
    let split := M.prefixSplitEquiv tau htau
    IM.center (split (.inl l)) ≤
      canonicalPrefixBoundary M n W tau htau := by
  dsimp only
  let IM := canonicalIntervalMeshOfAnchors M hdelta hn hW hWTwo S epsilon
    anchors hAnchors hInteriorLower hInteriorUpper
  let split := M.prefixSplitEquiv tau htau
  change IM.center (split (.inl l)) ≤
    canonicalPrefixBoundary M n W tau htau
  have hcenter := IM.center_le_upper (split (.inl l))
  have hmono : Monotone (fullCutoff M n W) :=
    fullCutoff_monotone M hdelta hn (W_le_first_fullCutoff M S)
  have hidx : (split (.inl l)).1 + 1 ≤ M.prefixIndex tau htau + 1 := by
    change l.1 + 1 ≤ M.prefixIndex tau htau + 1
    have hl : l.1 < M.prefixIndex tau htau + 1 := l.2
    omega
  have hcut := hmono hidx
  have hy : 1 < y n := by
    rw [← Real.log_pos_iff (Scale.y_pos (Nat.zero_lt_of_lt hn)).le]
    rw [Scale.log_y (Nat.zero_lt_of_lt hn)]
    exact mul_pos (by norm_num) (Real.log_pos (by exact_mod_cast hn))
  have hlowerTwo : 2 ≤ fullCutoff M n W ((split (.inl l)).1 + 1) :=
    hWTwo.trans (hmono (Nat.zero_le _))
  have hcoord := realLogCoordinate_mono_nat hy hlowerTwo hcut
  exact hcenter.trans (by
    simpa only [canonicalIntervalMeshOfAnchors_upper,
      canonicalCertificate_upper, canonicalPrefixBoundary,
      actualCutoffCoordinate] using hcoord)

theorem canonicalPrefix_boundary_le_high_center
    (k : M.prefixHigh tau htau) :
    let IM := canonicalIntervalMeshOfAnchors M hdelta hn hW hWTwo S epsilon
      anchors hAnchors hInteriorLower hInteriorUpper
    let split := M.prefixSplitEquiv tau htau
    canonicalPrefixBoundary M n W tau htau ≤
      IM.center (split (.inr k)) := by
  dsimp only
  let IM := canonicalIntervalMeshOfAnchors M hdelta hn hW hWTwo S epsilon
    anchors hAnchors hInteriorLower hInteriorUpper
  let split := M.prefixSplitEquiv tau htau
  change canonicalPrefixBoundary M n W tau htau ≤
    IM.center (split (.inr k))
  have hcenter := IM.lower_le_center (split (.inr k))
  have hmono : Monotone (fullCutoff M n W) :=
    fullCutoff_monotone M hdelta hn (W_le_first_fullCutoff M S)
  have hidx : M.prefixIndex tau htau + 1 ≤ (split (.inr k)).1 := by
    change M.prefixIndex tau htau + 1 ≤
      M.prefixIndex tau htau + 1 + k.1
    omega
  have hcut := hmono hidx
  have hy : 1 < y n := by
    rw [← Real.log_pos_iff (Scale.y_pos (Nat.zero_lt_of_lt hn)).le]
    rw [Scale.log_y (Nat.zero_lt_of_lt hn)]
    exact mul_pos (by norm_num) (Real.log_pos (by exact_mod_cast hn))
  have hlowerTwo : 2 ≤ fullCutoff M n W (M.prefixIndex tau htau + 1) :=
    hWTwo.trans (hmono (Nat.zero_le _))
  have hcoord := realLogCoordinate_mono_nat hy hlowerTwo hcut
  have hcoord' : canonicalPrefixBoundary M n W tau htau ≤
      IM.lower (split (.inr k)) := by
    simpa only [canonicalIntervalMeshOfAnchors_lower,
      canonicalCertificate_lower, canonicalPrefixBoundary,
      actualCutoffCoordinate] using hcoord
  exact hcoord'.trans hcenter

theorem sum_canonicalPrefix_low_length_eq :
    let IM := canonicalIntervalMeshOfAnchors M hdelta hn hW hWTwo S epsilon
      anchors hAnchors hInteriorLower hInteriorUpper
    let split := M.prefixSplitEquiv tau htau
    (∑ l : M.prefixLow tau htau, IM.length (split (.inl l))) =
      canonicalPrefixBoundary M n W tau htau -
        actualCutoffCoordinate M n W 0 := by
  dsimp only
  let j := M.prefixIndex tau htau
  change (∑ l : Fin (j + 1),
      (fun r : ℕ ↦ actualCutoffCoordinate M n W (r + 1) -
        actualCutoffCoordinate M n W r) l.1) =
      actualCutoffCoordinate M n W (j + 1) -
        actualCutoffCoordinate M n W 0
  calc
    _ = ∑ r ∈ Finset.range (j + 1),
        (actualCutoffCoordinate M n W (r + 1) -
          actualCutoffCoordinate M n W r) :=
      Fin.sum_univ_eq_sum_range _ (j + 1)
    _ = _ := by rw [Finset.sum_range_sub]

theorem sum_canonicalPrefix_low_length_le_boundary :
    let IM := canonicalIntervalMeshOfAnchors M hdelta hn hW hWTwo S epsilon
      anchors hAnchors hInteriorLower hInteriorUpper
    let split := M.prefixSplitEquiv tau htau
    (∑ l : M.prefixLow tau htau, IM.length (split (.inl l))) ≤
      canonicalPrefixBoundary M n W tau htau := by
  dsimp only
  rw [sum_canonicalPrefix_low_length_eq M hdelta hn hW hWTwo S htau
    anchors hAnchors hInteriorLower hInteriorUpper]
  have hbase : 0 ≤ actualCutoffCoordinate M n W 0 := by
    simp only [actualCutoffCoordinate, fullCutoff_zero, realLogCoordinate]
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast
      (show 1 ≤ W by omega)))
      (Real.log_nonneg (by
        have hy : 1 < y n := by
          rw [← Real.log_pos_iff (Scale.y_pos
            (Nat.zero_lt_of_lt hn)).le]
          rw [Scale.log_y (Nat.zero_lt_of_lt hn)]
          exact mul_pos (by norm_num)
            (Real.log_pos (by exact_mod_cast hn))
        exact hy.le))
  linarith

theorem sum_canonical_all_length_le_one :
    let IM := canonicalIntervalMeshOfAnchors M hdelta hn hW hWTwo S epsilon
      anchors hAnchors hInteriorLower hInteriorUpper
    (∑ i : Fin (M.cellCount + 1), IM.length i) ≤ 1 := by
  dsimp only
  let m := M.cellCount + 1
  change (∑ i : Fin m,
      (fun r : ℕ ↦ actualCutoffCoordinate M n W (r + 1) -
        actualCutoffCoordinate M n W r) i.1) ≤ 1
  have hsum : (∑ i : Fin m,
      (fun r : ℕ ↦ actualCutoffCoordinate M n W (r + 1) -
        actualCutoffCoordinate M n W r) i.1) =
      ∑ r ∈ Finset.range m,
        (actualCutoffCoordinate M n W (r + 1) -
          actualCutoffCoordinate M n W r) :=
    Fin.sum_univ_eq_sum_range
      (fun r : ℕ ↦ actualCutoffCoordinate M n W (r + 1) -
        actualCutoffCoordinate M n W r) m
  rw [hsum, Finset.sum_range_sub]
  have htop : actualCutoffCoordinate M n W m ≤ 1 := by
    have hfloor : (yNat n : ℝ) ≤ y n :=
      Nat.floor_le (Scale.y_pos (Nat.zero_lt_of_lt hn)).le
    have hy : 1 < y n := by
      rw [← Real.log_pos_iff (Scale.y_pos (Nat.zero_lt_of_lt hn)).le]
      rw [Scale.log_y (Nat.zero_lt_of_lt hn)]
      exact mul_pos (by norm_num) (Real.log_pos (by exact_mod_cast hn))
    have hmono := fullCutoff_monotone M hdelta hn
      (W_le_first_fullCutoff M S)
    have hFullTwo : 2 ≤ fullCutoff M n W m :=
      hWTwo.trans (hmono (Nat.zero_le m))
    have hFullY : (fullCutoff M n W m : ℝ) ≤ y n := by
      have hFullNat : fullCutoff M n W m ≤ yNat n := by
        rw [show m = M.cellCount + 1 by rfl, fullCutoff_last M
          (Nat.zero_lt_of_lt hn)]
      exact (by exact_mod_cast hFullNat :
        (fullCutoff M n W m : ℝ) ≤ (yNat n : ℝ)) |>.trans hfloor
    simp only [actualCutoffCoordinate, realLogCoordinate]
    exact (div_le_one (Real.log_pos hy)).2
      (Real.log_le_log (by exact_mod_cast
        (show 0 < fullCutoff M n W m by omega)) hFullY)
  have hbase : 0 ≤ actualCutoffCoordinate M n W 0 := by
    simp only [actualCutoffCoordinate, fullCutoff_zero, realLogCoordinate]
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast
      (show 1 ≤ W by omega)))
      (Real.log_pos (by
        rw [← Real.log_pos_iff (Scale.y_pos
          (Nat.zero_lt_of_lt hn)).le]
        rw [Scale.log_y (Nat.zero_lt_of_lt hn)]
        exact mul_pos (by norm_num)
          (Real.log_pos (by exact_mod_cast hn)))).le
  linarith

include hIdealAnchorLower in
theorem canonicalPrefix_low_anchor_zero
    (l : M.prefixLow tau htau) :
    let IM := canonicalIntervalMeshOfAnchors M hdelta hn hW hWTwo S epsilon
      anchors hAnchors hInteriorLower hInteriorUpper
    let split := M.prefixSplitEquiv tau htau
    IM.anchor (split (.inl l)) = 0 := by
  dsimp only
  let IM := canonicalIntervalMeshOfAnchors M hdelta hn hW hWTwo S epsilon
    anchors hAnchors hInteriorLower hInteriorUpper
  let split := M.prefixSplitEquiv tau htau
  change IM.anchor (split (.inl l)) = 0
  unfold IntervalMesh.anchor
  rw [if_neg]
  intro hmem
  change (split (.inl l)) ∈
    anchors.map (positiveBandEmbedding M) at hmem
  rw [Finset.mem_map] at hmem
  obtain ⟨k, hk, heq⟩ := hmem
  have hjk := M.prefixIndex_le_of_tau_lt_lower htau
    (hIdealAnchorLower k hk)
  have hval := congrArg Fin.val heq
  change k.1 + 1 = l.1 at hval
  have hl : l.1 < M.prefixIndex tau htau + 1 := l.2
  omega

include hIdealAnchorLower in
theorem sum_canonicalPrefix_high_anchor_eq_all :
    let IM := canonicalIntervalMeshOfAnchors M hdelta hn hW hWTwo S epsilon
      anchors hAnchors hInteriorLower hInteriorUpper
    let split := M.prefixSplitEquiv tau htau
    (∑ k : M.prefixHigh tau htau, IM.splitHighAnchor split k) =
      ∑ i : Fin (M.cellCount + 1), IM.anchor i := by
  dsimp only
  let IM := canonicalIntervalMeshOfAnchors M hdelta hn hW hWTwo S epsilon
    anchors hAnchors hInteriorLower hInteriorUpper
  let split := M.prefixSplitEquiv tau htau
  change (∑ k : M.prefixHigh tau htau, IM.splitHighAnchor split k) =
    ∑ i : Fin (M.cellCount + 1), IM.anchor i
  have hsum := Equiv.sum_comp split IM.anchor
  rw [Fintype.sum_sum_type] at hsum
  have hlow : (∑ l : M.prefixLow tau htau,
      IM.anchor (split (.inl l))) = 0 := by
    apply Finset.sum_eq_zero
    intro l _hl
    exact canonicalPrefix_low_anchor_zero M hdelta hn hW hWTwo S htau
      anchors hAnchors hIdealAnchorLower hInteriorLower hInteriorUpper l
  unfold IntervalMesh.splitHighAnchor
  linarith

end LiteralGeometry

end Mesh
end Erdos390.Full.RegularMeshPrimeCutoffs
