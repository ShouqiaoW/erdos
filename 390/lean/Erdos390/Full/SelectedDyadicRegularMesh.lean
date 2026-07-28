import Erdos390.Full.RegularRelativeMesh

/-!
# An explicit arbitrarily fine regular mesh with a fixed anchor block

For integers `K ≥ 3`, `N ≥ 1`, adjacent endpoints have ratio
`exp(log 2 / N)`.  The mesh runs from `2^{-K}` to `1`, and the consecutive
block of cells between `1/4` and `1/2` has total width exactly `1/4`.
Increasing `K` shrinks the moving-low cutoff; increasing `N` refines every
positive cell, without shrinking that total interior anchor mass.
-/

open scoped BigOperators
open Filter Topology

noncomputable section

namespace Erdos390.Full.SelectedDyadicRegularMesh

open RegularRelativeMesh

def delta (K : ℕ) : ℝ := (1 / 2 : ℝ) ^ K

def ratio (N : ℕ) : ℝ := Real.exp (Real.log 2 / (N : ℝ)) - 1

theorem one_add_ratio (N : ℕ) :
    1 + ratio N = Real.exp (Real.log 2 / (N : ℝ)) := by
  unfold ratio
  ring

theorem ratio_pos {N : ℕ} (hN : 0 < N) : 0 < ratio N := by
  rw [ratio, sub_pos, Real.one_lt_exp_iff]
  exact div_pos (Real.log_pos (by norm_num)) (by exact_mod_cast hN)

theorem ratio_pow_N {N : ℕ} (hN : 0 < N) :
    (1 + ratio N) ^ N = 2 := by
  rw [one_add_ratio, ← Real.exp_nat_mul]
  have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  rw [show (N : ℝ) * (Real.log 2 / (N : ℝ)) = Real.log 2 by
    field_simp [hNreal]]
  exact Real.exp_log (by norm_num)

/-- The explicit dyadic regular mesh. -/
def mesh (K N : ℕ) (hK : 0 < K) (hN : 0 < N) :
    Mesh (delta K) (ratio N) where
  cellCount := K * N
  cellCount_pos := Nat.mul_pos hK hN
  ratio := ratio N
  ratio_pos := ratio_pos hN
  ratio_le_eta := le_rfl
  lastEndpoint := by
    rw [delta, one_add_ratio, Nat.mul_comm K N, pow_mul]
    have hpow : Real.exp (Real.log 2 / (N : ℝ)) ^ N = 2 := by
      simpa only [← one_add_ratio] using ratio_pow_N hN
    rw [hpow]
    rw [← mul_pow]
    norm_num

theorem mesh_endpoint_blockLower
    {K N : ℕ} (hK : 3 ≤ K) (hN : 0 < N) :
    (mesh K N (by omega) hN).endpoint ((K - 2) * N) = 1 / 4 := by
  let M := mesh K N (by omega : 0 < K) hN
  have hpow : (1 + ratio N) ^ N = 2 := ratio_pow_N hN
  change delta K * (1 + ratio N) ^ ((K - 2) * N) = 1 / 4
  rw [Nat.mul_comm (K - 2) N, pow_mul, hpow]
  rw [show K = (K - 2) + 2 by omega, delta, pow_add]
  calc
    (1 / 2 : ℝ) ^ (K - 2) * (1 / 2 : ℝ) ^ 2 * 2 ^ (K - 2) =
        ((1 / 2 : ℝ) * 2) ^ (K - 2) * (1 / 2 : ℝ) ^ 2 := by
      rw [mul_pow]
      ring
    _ = 1 / 4 := by norm_num

theorem mesh_endpoint_blockUpper
    {K N : ℕ} (hK : 3 ≤ K) (hN : 0 < N) :
    (mesh K N (by omega) hN).endpoint ((K - 1) * N) = 1 / 2 := by
  let M := mesh K N (by omega : 0 < K) hN
  have hpow : (1 + ratio N) ^ N = 2 := ratio_pow_N hN
  change delta K * (1 + ratio N) ^ ((K - 1) * N) = 1 / 2
  rw [Nat.mul_comm (K - 1) N, pow_mul, hpow]
  rw [show K = (K - 1) + 1 by omega, delta, pow_add]
  calc
    (1 / 2 : ℝ) ^ (K - 1) * (1 / 2 : ℝ) ^ 1 * 2 ^ (K - 1) =
        ((1 / 2 : ℝ) * 2) ^ (K - 1) * (1 / 2 : ℝ) := by
      rw [mul_pow]
      ring
    _ = 1 / 2 := by norm_num

private def blockSubtype (K N : ℕ) :=
  {i : ℕ // i ∈ Finset.Ico ((K - 2) * N) ((K - 1) * N)}

private def blockEmbedding
    {K N : ℕ} (hK : 3 ≤ K) (hN : 0 < N) :
    blockSubtype K N ↪ Fin ((mesh K N (by omega) hN).cellCount) where
  toFun i := ⟨i.1, by
    have hi := (Finset.mem_Ico.mp i.2).2
    change i.1 < K * N
    exact hi.trans_le (Nat.mul_le_mul_right N (by omega : K - 1 ≤ K))⟩
  inj' := by
    intro i j hij
    apply Subtype.ext
    exact congrArg Fin.val hij

/-- Consecutive positive cells whose ideal union is `[1/4,1/2]`. -/
def anchors {K N : ℕ} (hK : 3 ≤ K) (hN : 0 < N) :
    Finset (Fin ((mesh K N (by omega) hN).cellCount)) :=
  (Finset.Ico ((K - 2) * N) ((K - 1) * N)).attach.map
    (blockEmbedding hK hN)

theorem anchors_nonempty {K N : ℕ} (hK : 3 ≤ K) (hN : 0 < N) :
    (anchors hK hN).Nonempty := by
  have hab : (K - 2) * N < (K - 1) * N := by
    exact (Nat.mul_lt_mul_right hN).2 (by omega)
  have hmem : (K - 2) * N ∈
      Finset.Ico ((K - 2) * N) ((K - 1) * N) :=
    Finset.mem_Ico.mpr ⟨le_rfl, hab⟩
  let i : blockSubtype K N := ⟨(K - 2) * N, hmem⟩
  exact ⟨blockEmbedding hK hN i, by
    unfold anchors
    exact (Finset.mem_map' (blockEmbedding hK hN)).2
      (Finset.mem_attach _ i)⟩

theorem mem_anchors_index_bounds
    {K N : ℕ} (hK : 3 ≤ K) (hN : 0 < N)
    {k : Fin ((mesh K N (lt_of_lt_of_le (by decide : 0 < 3) hK) hN).cellCount)}
    (hk : k ∈ anchors hK hN) :
    (K - 2) * N ≤ k.1 ∧ k.1 < (K - 1) * N := by
  rw [anchors, Finset.mem_map] at hk
  obtain ⟨i, hi, rfl⟩ := hk
  exact Finset.mem_Ico.mp i.2

theorem anchors_ideal_interior
    {K N : ℕ} (hK : 3 ≤ K) (hN : 0 < N)
    {k : Fin ((mesh K N (lt_of_lt_of_le (by decide : 0 < 3) hK) hN).cellCount)}
    (hk : k ∈ anchors hK hN) :
    1 / 8 < (mesh K N (by omega) hN).lower k ∧
      (mesh K N (by omega) hN).upper k ≤ 1 - 1 / 8 := by
  let M := mesh K N (by omega : 0 < K) hN
  obtain ⟨hka, hkb⟩ := mem_anchors_index_bounds hK hN hk
  have hbase : 1 ≤ 1 + M.ratio := by linarith [M.ratio_pos]
  have hmono : Monotone M.endpoint := by
    intro a b hab
    unfold RegularRelativeMesh.Mesh.endpoint
    have hdelta0 : 0 ≤ delta K := by
      unfold delta
      positivity
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hbase hab)
      hdelta0
  have hlo : (1 / 4 : ℝ) ≤ M.lower k := by
    rw [← mesh_endpoint_blockLower hK hN]
    exact hmono hka
  have hhi : M.upper k ≤ (1 / 2 : ℝ) := by
    rw [← mesh_endpoint_blockUpper hK hN]
    apply hmono
    change k.1 + 1 ≤ (K - 1) * N
    omega
  constructor
  · linarith
  · linarith

theorem sum_anchor_widths
    {K N : ℕ} (hK : 3 ≤ K) (hN : 0 < N) :
    ∑ k ∈ anchors hK hN, (mesh K N (by omega) hN).width k = 1 / 4 := by
  let M := mesh K N (by omega : 0 < K) hN
  unfold anchors
  rw [Finset.sum_map]
  change (∑ i ∈ (Finset.Ico ((K - 2) * N) ((K - 1) * N)).attach,
      M.width (blockEmbedding hK hN i)) = 1 / 4
  have hattach :
      (∑ i ∈ (Finset.Ico ((K - 2) * N) ((K - 1) * N)).attach,
          M.width (blockEmbedding hK hN i)) =
        (∑ i ∈ Finset.Ico ((K - 2) * N) ((K - 1) * N),
          (M.endpoint (i + 1) - M.endpoint i)) := by
    calc
      (∑ i ∈ (Finset.Ico ((K - 2) * N) ((K - 1) * N)).attach,
          M.width (blockEmbedding hK hN i)) =
          ∑ i ∈ (Finset.Ico ((K - 2) * N) ((K - 1) * N)).attach,
            (M.endpoint (i.1 + 1) - M.endpoint i.1) := by
        apply Finset.sum_congr rfl
        intro i hi
        rfl
      _ = ∑ i ∈ Finset.Ico ((K - 2) * N) ((K - 1) * N),
          (M.endpoint (i + 1) - M.endpoint i) :=
        by
          simpa only using (Finset.sum_attach
            (Finset.Ico ((K - 2) * N) ((K - 1) * N))
            (fun i ↦ M.endpoint (i + 1) - M.endpoint i))
  rw [hattach]
  have htel := Finset.sum_Ico_sub M.endpoint
    (Nat.mul_le_mul_right N (by omega : K - 2 ≤ K - 1))
  rw [htel]
  rw [mesh_endpoint_blockUpper hK hN, mesh_endpoint_blockLower hK hN]
  norm_num

theorem delta_tendsto_zero : Tendsto delta atTop (nhds 0) := by
  unfold delta
  exact tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by norm_num)

theorem ratio_tendsto_zero : Tendsto ratio atTop (nhds 0) := by
  have hcast : Tendsto (fun N : ℕ ↦ (N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun N : ℕ ↦ ((N : ℝ))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hcast
  have hquot : Tendsto (fun N : ℕ ↦ Real.log 2 / (N : ℝ)) atTop
      (nhds 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using tendsto_const_nhds.mul hinv
  have hexp := Real.continuous_exp.continuousAt.tendsto.comp hquot
  have hone : Tendsto (fun _N : ℕ ↦ (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  simpa only [ratio, Real.exp_zero, sub_self] using hexp.sub hone

/-- Both the low cell and every positive relative cell can be made finer
than an arbitrary prescribed tolerance, while the anchor block stays fixed. -/
theorem exists_fine_mesh (tol : ℝ) (htol : 0 < tol) :
    ∃ K N : ℕ, ∃ hK : 3 ≤ K, ∃ hN : 0 < N,
      delta K < tol ∧ ratio N < tol ∧
      ∀ k : Fin ((mesh K N (by omega) hN).cellCount),
        (mesh K N (by omega) hN).width k < tol := by
  obtain ⟨K0, hK0⟩ := eventually_atTop.1
    (delta_tendsto_zero.eventually (eventually_lt_nhds htol))
  obtain ⟨N0, hN0⟩ := eventually_atTop.1
    (ratio_tendsto_zero.eventually (eventually_lt_nhds htol))
  let K := max 3 K0
  let N := max 1 N0
  have hK : 3 ≤ K := le_max_left _ _
  have hN : 0 < N := by exact (by omega : 0 < max 1 N0)
  have hdelta : delta K < tol := hK0 K (le_max_right _ _)
  have hratio : ratio N < tol := hN0 N (le_max_right _ _)
  refine ⟨K, N, hK, hN, hdelta, hratio, ?_⟩
  intro k
  rw [(mesh K N (by omega) hN).width_eq_ratio_mul_lower]
  have hlower : (mesh K N (by omega) hN).lower k ≤ 1 :=
    (mesh K N (by omega) hN).lower_lt_upper (by
      unfold delta
      positivity) k |>.le.trans
      ((mesh K N (by omega) hN).upper_le_one (by
        unfold delta
        positivity) k)
  have hrnonneg : 0 ≤ ratio N := (ratio_pos hN).le
  calc
    ratio N * (mesh K N (by omega) hN).lower k ≤ ratio N * 1 :=
      mul_le_mul_of_nonneg_left hlower hrnonneg
    _ < tol := by simpa only [mul_one] using hratio

end Erdos390.Full.SelectedDyadicRegularMesh
