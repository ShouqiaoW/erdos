import Erdos390.Full.PaperCanonicalPrimeGraphActualSchurEventually

/-!
# Literal sharp solution form of paper Lemma 8.5

The exact arithmetic nuisance-Schur equivalence is converted here into the
form consumed by the nonlinear fitting argument: every sharp arithmetic
right side has one and only one solution, and every normalized coordinate
`|q_i| / alpha_i` is bounded by the same structural inverse constant.
-/

open Filter Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry PaperWeightedInverseExport
open PaperGuardCensus RegularMeshPrimeCutoffs

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]

/-- On the literal arithmetic gauge, the paper's sharp norm bound is
equivalent to the rowwise relative bound. -/
theorem paperSharpNorm_le_iff_abs_coordinate_le
    (B : BridgeData Head Band) {K : ℝ} (hK : 0 ≤ K)
    (b : B.RawBandGauge) :
    paperSharpNorm B.harmonicMass B.bandCenter
        (B.partition.center_ne_zero B.n_gt_one) b ≤ K ↔
      ∀ i : Band, |b.1 i| ≤ K * B.bandCenter i := by
  constructor
  · intro hsharp i
    have hcoord := abs_raw_coordinate_le_paperSharpNorm
      B.harmonicMass B.bandCenter
      (B.partition.center_ne_zero B.n_gt_one) b i
    have hcenter : 0 ≤ B.bandCenter i := (B.bandCenter_pos i).le
    calc
      |b.1 i| ≤ |B.bandCenter i| *
          paperSharpNorm B.harmonicMass B.bandCenter
            (B.partition.center_ne_zero B.n_gt_one) b := hcoord
      _ ≤ B.bandCenter i * K := by
        rw [abs_of_nonneg hcenter]
        exact mul_le_mul_of_nonneg_left hsharp hcenter
      _ = K * B.bandCenter i := by ring
  · intro hcoord
    rw [paperSharpNorm_eq_piNorm,
      pi_norm_le_iff_of_nonneg hK]
    intro i
    have hcenter : 0 < B.bandCenter i := B.bandCenter_pos i
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hcenter]
    exact (div_le_iff₀ hcenter).2 (hcoord i)

/-- Reusable finite-dimensional solution API.  It records uniqueness for
the literal map, rather than merely uniqueness among vectors satisfying the
displayed estimates. -/
theorem exists_unique_actualBandSchur_sharp_solution_of_equiv
    (B : BridgeData Head Band) [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (he : ∀ q, e q = B.actualBandSchurLinearMap xi hgamma hgap q)
    {C : ℝ}
    (hinv : ∀ v,
      paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one) (e.symm v) ≤
        C * paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one) v)
    (b : B.RawBandGauge) :
    ∃ q : B.RawBandGauge,
      B.actualBandSchurLinearMap xi hgamma hgap q = b ∧
      (∀ q' : B.RawBandGauge,
        B.actualBandSchurLinearMap xi hgamma hgap q' = b → q' = q) ∧
      paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one) q ≤
        C * paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one) b ∧
      ∀ i : Band,
        |q.1 i| / B.bandCenter i ≤
          C * paperSharpNorm B.harmonicMass B.bandCenter
            (B.partition.center_ne_zero B.n_gt_one) b := by
  let q : B.RawBandGauge := e.symm b
  have hsolve : B.actualBandSchurLinearMap xi hgamma hgap q = b := by
    rw [← he q]
    exact e.apply_symm_apply b
  have hunique : ∀ q' : B.RawBandGauge,
      B.actualBandSchurLinearMap xi hgamma hgap q' = b → q' = q := by
    intro q' hq'
    apply e.injective
    rw [he q', he q, hq', hsolve]
  have hsharp :
      paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one) q ≤
        C * paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one) b := by
    exact hinv b
  refine ⟨q, hsolve, hunique, hsharp, ?_⟩
  intro i
  have hcoord := abs_raw_coordinate_le_paperSharpNorm
    B.harmonicMass B.bandCenter
    (B.partition.center_ne_zero B.n_gt_one) q i
  have hcenter : 0 < B.bandCenter i := B.bandCenter_pos i
  calc
    |q.1 i| / B.bandCenter i ≤
        (|B.bandCenter i| *
          paperSharpNorm B.harmonicMass B.bandCenter
            (B.partition.center_ne_zero B.n_gt_one) q) /
          B.bandCenter i :=
      div_le_div_of_nonneg_right hcoord hcenter.le
    _ = paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one) q := by
      rw [abs_of_pos hcenter]
      field_simp [hcenter.ne']
    _ ≤ C * paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one) b := hsharp

set_option maxHeartbeats 1000000 in
/-- Anchor-free, paper-order eventual solution form of Lemma 8.5.  The
constant and prime cutoff precede the mesh, the exact head family, and the
effective ball.  All analytic estimates needed to construct the solution
are discharged by the preceding prime-graph terminal. -/
theorem exists_fineMesh_cutoff_eventually_unique_actualBandSchur_sharp_solution :
    ∃ meshTol : ℝ, 0 < meshTol ∧
      ∃ Csolve : ℝ, 0 < Csolve ∧
      ∃ W₀ : ℕ,
      ∀ W : ℕ, W₀ ≤ W →
      ∀ {delta eta : ℝ} (M : RegularRelativeMesh.Mesh delta eta)
        (hdelta : 0 < delta),
        delta + M.ratio ≤ meshTol →
        ∀ (Head : Type*) [Fintype Head] [DecidableEq Head] [Nonempty Head],
        ∀ (Phead : Head → HeadPattern.Pattern),
          (∀ h : Head, ∀ p : ℕ,
            p ∈ (Phead h).primes ↔ p.Prime ∧ p ≤ W) →
        ∀ (I : PhysicalIntervals) (U : ℝ) (hU : 1 ≤ U)
          (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
          (hupperU : ∀ sigma, I.upper sigma ≤ U),
        ∀ (Cprom Cbank : ℕ) (ledger : ∀ n, Ledger n Cprom Cbank),
        ∀ (a : NNReal) (marginFloor : ℝ), 0 < marginFloor →
        ∀ᶠ n : ℕ in atTop,
          ∀ (B : BridgeData Head (Fin (M.cellCount + 1))),
            B.sampleData.n = n → B.sampleData.W = W →
            ∀ (hBWlarge : 1 < B.sampleData.W),
          ∀ (hsep : physicalBound (I.upper .minus) B.sampleData.n <
              physicalBound (I.lower .plus) B.sampleData.n)
            (hremaining : ∀ c : Cell Head,
              (rawCell Phead I B.sampleData.n c \
                (ledger B.sampleData.n).guards).Nonempty),
            (hcanonical : B.sampleData = canonicalSampleData
              (W := B.sampleData.W) Phead I (ledger B.sampleData.n)
                hsep hremaining) →
            (∃ (hWne : B.sampleData.W ≠ 0)
                (S : ScaleSeparation M B.sampleData.n B.sampleData.W),
              B.partition = Mesh.canonicalPartition
                M hdelta B.n_gt_one hWne S) →
            ∀ (T : BarycentricTarget B.sampleData)
              (_hTmargin : marginFloor ≤ T.cellMassMargin)
              (hbaseline : B.baseline = T.baseline)
              (z : B.EffectiveParamSpace)
              (hz : z ∈ closedBall
                (0 : B.EffectiveParamSpace) (a : ℝ))
              (b : B.RawBandGauge),
              let hgamma := B.canonicalEffectiveNuisanceGamma_pos
                I U (3 * (a : ℝ)) T
              let hgap := B.canonicalEffectiveNuisanceGap_on_closedBall I a
                hU hlowerOne hupperU
                (by intro sigma; rw [hcanonical]; rfl)
                (by intro sigma; rw [hcanonical]; rfl)
                T hbaseline hBWlarge z hz
              ∃ q : B.RawBandGauge,
                B.actualBandSchurLinearMap (B.effectiveParamEquiv z)
                    hgamma hgap q = b ∧
                (∀ q' : B.RawBandGauge,
                  B.actualBandSchurLinearMap (B.effectiveParamEquiv z)
                    hgamma hgap q' = b → q' = q) ∧
                paperSharpNorm B.harmonicMass B.bandCenter
                    (B.partition.center_ne_zero B.n_gt_one) q ≤
                  Csolve * paperSharpNorm B.harmonicMass B.bandCenter
                    (B.partition.center_ne_zero B.n_gt_one) b ∧
                ∀ i : Fin (M.cellCount + 1),
                  |q.1 i| / B.bandCenter i ≤
                    Csolve * paperSharpNorm B.harmonicMass B.bandCenter
                      (B.partition.center_ne_zero B.n_gt_one) b := by
  obtain ⟨meshTol, hmeshTol, Csolve, hCsolve, W₀, hmain⟩ :=
    @exists_fineMesh_cutoff_eventually_actualBandSchur_primeGraph_inverse
  refine ⟨meshTol, hmeshTol, Csolve, hCsolve, W₀, ?_⟩
  intro W hW delta eta M hdelta hmesh Head _instFintype _instDecidable
    _instNonempty Phead hhead I U hU hlowerOne hupperU Cprom Cbank
    ledger a marginFloor hmarginFloor
  have hterminal := hmain W hW M hdelta hmesh Head Phead hhead
    I U hU hlowerOne hupperU Cprom Cbank ledger a marginFloor hmarginFloor
  filter_upwards [hterminal] with n hn
  intro B hBn hBW hBWlarge hsep hremaining hcanonical hpartition T
    hTmargin hbaseline z hz b
  obtain ⟨e, he, hinv⟩ := hn B hBn hBW hBWlarge hsep hremaining
    hcanonical hpartition T hTmargin hbaseline
  dsimp only
  exact B.exists_unique_actualBandSchur_sharp_solution_of_equiv
    (B.effectiveParamEquiv z)
    (B.canonicalEffectiveNuisanceGamma_pos I U (3 * (a : ℝ)) T)
    (B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
      hlowerOne hupperU
      (by intro sigma; rw [hcanonical]; rfl)
      (by intro sigma; rw [hcanonical]; rfl)
      T hbaseline hBWlarge z hz)
    (e z hz) (he z hz) (hinv z hz) b

set_option maxHeartbeats 1200000 in
/-- Paper-literal row-scaled form of Lemma 8.5.  If the projected right side
has size `C * w * alpha_i`, where `w = delta + M.ratio`, then the unique
solution has size `Csharp * w * alpha_i`.  The witness `Csharp` is chosen
before `W`, the mesh, the head family, and the tilt ball. -/
theorem exists_fineMesh_cutoff_eventually_actualBandSchur_coordinate_solution
    (C : ℝ) (hC : 0 < C) :
    ∃ meshTol : ℝ, 0 < meshTol ∧
      ∃ Csharp : ℝ, 0 < Csharp ∧
      ∃ W₀ : ℕ,
      ∀ W : ℕ, W₀ ≤ W →
      ∀ {delta eta : ℝ} (M : RegularRelativeMesh.Mesh delta eta)
        (hdelta : 0 < delta),
        delta + M.ratio ≤ meshTol →
        ∀ (Head : Type*) [Fintype Head] [DecidableEq Head] [Nonempty Head],
        ∀ (Phead : Head → HeadPattern.Pattern),
          (∀ h : Head, ∀ p : ℕ,
            p ∈ (Phead h).primes ↔ p.Prime ∧ p ≤ W) →
        ∀ (I : PhysicalIntervals) (U : ℝ) (hU : 1 ≤ U)
          (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
          (hupperU : ∀ sigma, I.upper sigma ≤ U),
        ∀ (Cprom Cbank : ℕ) (ledger : ∀ n, Ledger n Cprom Cbank),
        ∀ (a : NNReal) (marginFloor : ℝ), 0 < marginFloor →
        ∀ᶠ n : ℕ in atTop,
          ∀ (B : BridgeData Head (Fin (M.cellCount + 1))),
            B.sampleData.n = n → B.sampleData.W = W →
            ∀ (hBWlarge : 1 < B.sampleData.W),
          ∀ (hsep : physicalBound (I.upper .minus) B.sampleData.n <
              physicalBound (I.lower .plus) B.sampleData.n)
            (hremaining : ∀ c : Cell Head,
              (rawCell Phead I B.sampleData.n c \
                (ledger B.sampleData.n).guards).Nonempty),
            (hcanonical : B.sampleData = canonicalSampleData
              (W := B.sampleData.W) Phead I (ledger B.sampleData.n)
                hsep hremaining) →
            (∃ (hWne : B.sampleData.W ≠ 0)
                (S : ScaleSeparation M B.sampleData.n B.sampleData.W),
              B.partition = Mesh.canonicalPartition
                M hdelta B.n_gt_one hWne S) →
            ∀ (T : BarycentricTarget B.sampleData)
              (_hTmargin : marginFloor ≤ T.cellMassMargin)
              (hbaseline : B.baseline = T.baseline)
              (z : B.EffectiveParamSpace)
              (hz : z ∈ closedBall
                (0 : B.EffectiveParamSpace) (a : ℝ))
              (b : B.RawBandGauge),
              (∀ i : Fin (M.cellCount + 1),
                |b.1 i| ≤ C * (delta + M.ratio) * B.bandCenter i) →
              let hgamma := B.canonicalEffectiveNuisanceGamma_pos
                I U (3 * (a : ℝ)) T
              let hgap := B.canonicalEffectiveNuisanceGap_on_closedBall I a
                hU hlowerOne hupperU
                (by intro sigma; rw [hcanonical]; rfl)
                (by intro sigma; rw [hcanonical]; rfl)
                T hbaseline hBWlarge z hz
              ∃ q : B.RawBandGauge,
                B.actualBandSchurLinearMap (B.effectiveParamEquiv z)
                    hgamma hgap q = b ∧
                (∀ q' : B.RawBandGauge,
                  B.actualBandSchurLinearMap (B.effectiveParamEquiv z)
                    hgamma hgap q' = b → q' = q) ∧
                paperSharpNorm B.harmonicMass B.bandCenter
                    (B.partition.center_ne_zero B.n_gt_one) q ≤
                  Csharp * (delta + M.ratio) ∧
                ∀ i : Fin (M.cellCount + 1),
                  |q.1 i| ≤
                    Csharp * (delta + M.ratio) * B.bandCenter i := by
  obtain ⟨meshTol, hmeshTol, Csolve, hCsolve, W₀, hmain⟩ :=
    @exists_fineMesh_cutoff_eventually_unique_actualBandSchur_sharp_solution
  let Csharp : ℝ := Csolve * C
  have hCsharp : 0 < Csharp := by
    dsimp only [Csharp]
    exact mul_pos hCsolve hC
  refine ⟨meshTol, hmeshTol, Csharp, hCsharp, W₀, ?_⟩
  intro W hW delta eta M hdelta hmesh Head _instFintype _instDecidable
    _instNonempty Phead hhead I U hU hlowerOne hupperU Cprom Cbank
    ledger a marginFloor hmarginFloor
  have hterminal := hmain W hW M hdelta hmesh Head Phead hhead
    I U hU hlowerOne hupperU Cprom Cbank ledger a marginFloor hmarginFloor
  filter_upwards [hterminal] with n hn
  intro B hBn hBW hBWlarge hsep hremaining hcanonical hpartition T
    hTmargin hbaseline z hz b hb
  have hsolution := hn B hBn hBW hBWlarge hsep hremaining hcanonical
    hpartition T hTmargin hbaseline z hz b
  dsimp only at hsolution ⊢
  obtain ⟨q, hsolve, hunique, hsharp, _hnormalized⟩ := hsolution
  have hw : 0 ≤ delta + M.ratio :=
    (add_pos hdelta M.ratio_pos).le
  have hbSharp :
      paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one) b ≤
        C * (delta + M.ratio) := by
    apply (B.paperSharpNorm_le_iff_abs_coordinate_le
      (mul_nonneg hC.le hw) b).2
    intro i
    exact hb i
  have hqSharp :
      paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one) q ≤
        Csharp * (delta + M.ratio) := by
    calc
      paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one) q ≤
          Csolve * paperSharpNorm B.harmonicMass B.bandCenter
            (B.partition.center_ne_zero B.n_gt_one) b := hsharp
      _ ≤ Csolve * (C * (delta + M.ratio)) :=
        mul_le_mul_of_nonneg_left hbSharp hCsolve.le
      _ = Csharp * (delta + M.ratio) := by
        dsimp only [Csharp]
        ring
  refine ⟨q, hsolve, hunique, hqSharp, ?_⟩
  intro i
  have hcoord := abs_raw_coordinate_le_paperSharpNorm
    B.harmonicMass B.bandCenter
    (B.partition.center_ne_zero B.n_gt_one) q i
  have hcenter : 0 ≤ B.bandCenter i := (B.bandCenter_pos i).le
  calc
    |q.1 i| ≤ |B.bandCenter i| *
        paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one) q := hcoord
    _ ≤ B.bandCenter i * (Csharp * (delta + M.ratio)) := by
      rw [abs_of_nonneg hcenter]
      exact mul_le_mul_of_nonneg_left hqSharp hcenter
    _ = Csharp * (delta + M.ratio) * B.bandCenter i := by ring

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
