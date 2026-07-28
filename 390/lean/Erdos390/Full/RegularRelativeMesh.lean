import Mathlib

/-!
# Existence of a finite regular relative mesh

Section 8.4 partitions the positive logarithmic interval `[delta,1]` into
geometric cells.  This file constructs such a mesh rather than leaving its
existence as a certificate.  Given `0 < delta < 1` and a requested upper
relative width `eta > 0`, the number of cells is the ceiling of the relevant
logarithmic ratio and the common relative width is adjusted so that the last
endpoint is exactly `1`.
-/

open scoped BigOperators

namespace Erdos390.Full.RegularRelativeMesh

noncomputable section

/-- Finite geometric mesh data.  The positive cells are indexed by
`Fin cellCount`; the separate moving-low cell `[t₀,delta]` is not part of
this structure. -/
structure Mesh (delta eta : ℝ) where
  cellCount : ℕ
  cellCount_pos : 0 < cellCount
  ratio : ℝ
  ratio_pos : 0 < ratio
  ratio_le_eta : ratio ≤ eta
  lastEndpoint : delta * (1 + ratio) ^ cellCount = 1

namespace Mesh

variable {delta eta : ℝ} (M : Mesh delta eta)

/-- Endpoint number `k`, extended to all natural `k`. -/
def endpoint (k : ℕ) : ℝ := delta * (1 + M.ratio) ^ k

/-- Lower endpoint of a positive cell. -/
def lower (k : Fin M.cellCount) : ℝ := M.endpoint k.1

/-- Upper endpoint of a positive cell. -/
def upper (k : Fin M.cellCount) : ℝ := M.endpoint (k.1 + 1)

/-- Cell width. -/
def width (k : Fin M.cellCount) : ℝ := M.upper k - M.lower k

theorem endpoint_zero : M.endpoint 0 = delta := by
  simp [endpoint]

theorem endpoint_cellCount : M.endpoint M.cellCount = 1 := by
  exact M.lastEndpoint

theorem endpoint_succ (k : ℕ) :
    M.endpoint (k + 1) = M.endpoint k * (1 + M.ratio) := by
  unfold endpoint
  rw [pow_succ]
  ring

theorem one_lt_one_add_ratio : 1 < 1 + M.ratio := by
  linarith [M.ratio_pos]

theorem endpoint_pos (hdelta : 0 < delta) (k : ℕ) :
    0 < M.endpoint k := by
  unfold endpoint
  exact mul_pos hdelta (pow_pos (by linarith [M.ratio_pos]) k)

theorem lower_pos (hdelta : 0 < delta) (k : Fin M.cellCount) :
    0 < M.lower k := M.endpoint_pos hdelta k.1

theorem width_eq_ratio_mul_lower (k : Fin M.cellCount) :
    M.width k = M.ratio * M.lower k := by
  unfold width upper lower
  rw [M.endpoint_succ]
  ring

theorem width_pos (hdelta : 0 < delta) (k : Fin M.cellCount) :
    0 < M.width k := by
  rw [M.width_eq_ratio_mul_lower]
  exact mul_pos M.ratio_pos (M.lower_pos hdelta k)

theorem lower_lt_upper (hdelta : 0 < delta) (k : Fin M.cellCount) :
    M.lower k < M.upper k := by
  rw [← sub_pos, ← width]
  exact M.width_pos hdelta k

theorem width_le_eta_mul_lower (k : Fin M.cellCount) :
    M.width k ≤ eta * M.lower k := by
  rw [M.width_eq_ratio_mul_lower]
  exact mul_le_mul_of_nonneg_right M.ratio_le_eta
    (le_of_lt (by
      unfold lower endpoint
      have hdelta : 0 < delta := by
        have hbase : 0 < (1 + M.ratio) ^ M.cellCount :=
          pow_pos (by linarith [M.ratio_pos]) M.cellCount
        nlinarith [M.lastEndpoint]
      exact mul_pos hdelta (pow_pos (by linarith [M.ratio_pos]) k.1)))

theorem upper_le_one (hdelta : 0 < delta) (k : Fin M.cellCount) :
    M.upper k ≤ 1 := by
  have hpow : (1 + M.ratio) ^ (k.1 + 1) ≤
      (1 + M.ratio) ^ M.cellCount :=
    pow_le_pow_right₀ (by linarith [M.ratio_pos]) (Nat.succ_le_iff.mpr k.2)
  unfold upper endpoint
  calc
    delta * (1 + M.ratio) ^ (k.1 + 1) ≤
        delta * (1 + M.ratio) ^ M.cellCount :=
      mul_le_mul_of_nonneg_left hpow hdelta.le
    _ = 1 := M.lastEndpoint

theorem upper_eq_next_lower {k : ℕ} (hk : k + 1 < M.cellCount) :
    M.upper ⟨k, Nat.lt_of_succ_lt hk⟩ =
      M.lower ⟨k + 1, hk⟩ := by
  rfl

/-- The positive cells telescope exactly from `delta` to `1`. -/
theorem sum_width_eq_one_sub_delta :
    ∑ k : Fin M.cellCount, M.width k = 1 - delta := by
  change (∑ k : Fin M.cellCount,
      (fun i : ℕ ↦ M.endpoint (i + 1) - M.endpoint i) k.1) =
    1 - delta
  calc
    (∑ k : Fin M.cellCount,
        (fun i : ℕ ↦ M.endpoint (i + 1) - M.endpoint i) k.1) =
        ∑ k ∈ Finset.range M.cellCount,
          (M.endpoint (k + 1) - M.endpoint k) :=
      Fin.sum_univ_eq_sum_range
        (fun i : ℕ ↦ M.endpoint (i + 1) - M.endpoint i) M.cellCount
    _ = 1 - delta := by
      rw [Finset.sum_range_sub, M.endpoint_cellCount, M.endpoint_zero]

end Mesh

/-- A geometric relative mesh always exists with common relative width no
larger than the requested `eta`. -/
theorem exists_mesh {delta eta : ℝ}
    (hdelta : 0 < delta) (hdeltaOne : delta < 1) (heta : 0 < eta) :
    Nonempty (Mesh delta eta) := by
  let A : ℝ := Real.log (1 / delta)
  let beta : ℝ := Real.log (1 + eta)
  have hinv : 1 < 1 / delta := by
    rw [lt_div_iff₀ hdelta]
    simpa only [one_mul] using hdeltaOne
  have hA : 0 < A := Real.log_pos hinv
  have hOneEta : 1 < 1 + eta := by linarith
  have hbeta : 0 < beta := Real.log_pos hOneEta
  let N : ℕ := ⌈A / beta⌉₊
  have hAB : 0 < A / beta := div_pos hA hbeta
  have hN : 0 < N := Nat.ceil_pos.mpr hAB
  have hceil : A / beta ≤ (N : ℝ) := Nat.le_ceil (A / beta)
  have hANbeta : A ≤ (N : ℝ) * beta := by
    exact (div_le_iff₀ hbeta).mp hceil
  have hNreal : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hdivLe : A / (N : ℝ) ≤ beta := by
    rw [div_le_iff₀ hNreal]
    simpa only [mul_comm] using hANbeta
  let rho : ℝ := Real.exp (A / (N : ℝ)) - 1
  have hrho : 0 < rho := by
    dsimp only [rho]
    rw [sub_pos, Real.one_lt_exp_iff]
    exact div_pos hA hNreal
  have hrhoEta : rho ≤ eta := by
    have hexp : Real.exp (A / (N : ℝ)) ≤ Real.exp beta :=
      Real.exp_le_exp.mpr hdivLe
    have hExpBeta : Real.exp beta = 1 + eta := by
      exact Real.exp_log (by linarith [heta])
    dsimp only [rho]
    rw [hExpBeta] at hexp
    linarith
  have hpow : (1 + rho) ^ N = Real.exp A := by
    have hone : 1 + rho = Real.exp (A / (N : ℝ)) := by
      dsimp only [rho]
      ring
    rw [hone, ← Real.exp_nat_mul]
    congr 1
    field_simp [ne_of_gt hNreal]
  have hExpA : Real.exp A = 1 / delta := by
    exact Real.exp_log (div_pos zero_lt_one hdelta)
  refine ⟨⟨N, hN, rho, hrho, hrhoEta, ?_⟩⟩
  rw [hpow, hExpA]
  field_simp [ne_of_gt hdelta]

end

end Erdos390.Full.RegularRelativeMesh
