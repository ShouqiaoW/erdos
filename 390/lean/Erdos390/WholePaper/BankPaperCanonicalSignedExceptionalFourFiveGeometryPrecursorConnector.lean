import Erdos390.WholePaper.BankPaperCanonicalSignedExceptionalOrderedMixtureConnector
import Erdos390.WholePaper.BankPaperCanonicalFourFiveKernelVariation
import Erdos390.Full.PaperPrimePowerTailRate

/-!
# Geometry precursors for the signed exceptional four/five chamber

This file supplies the elementary eventual inputs which precede the six
interval estimates in the signed exceptional four/five chamber.

* The natural exceptional cutoff is eventually at most half of `yNat`.
* Every frozen coordinate with smooth core in the deep prefix belongs to
  the padded chamber `[4.1, 4.7]`.
* The five routine scalar fields of the chamber input are packaged together.

The coordinate result is obtained directly from the existing common endpoint
geometry.  No rough-counting estimate or kernel estimate is introduced here.
-/

open Filter Topology

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale
open Erdos390.Full.PaperPrimePowerTailRate

noncomputable section

namespace BankPaperRealization

/-! ## Separation of the natural exceptional cutoff from `yNat` -/

/-- The exponent gap `deltaStar < 1/18 < 1/5`, including the ceiling loss,
eventually places twice the natural exceptional cutoff below `yNat`. -/
theorem eventually_two_mul_tangentPaperExceptionalCutoff_le_yNat
    {deltaStar : Real} (hdeltaUpper : deltaStar < 1 / 18) :
    ∀ᶠ n : Nat in atTop,
      2 * tangentPaperExceptionalCutoff deltaStar n <= yNat n := by
  have hrootTop :
      Tendsto (fun n : Nat => (n : Real) ^ (1 / 10 : Real))
        atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : Real) < 1 / 10)).comp
      tendsto_natCast_atTop_atTop
  filter_upwards [
      eventually_rpow_one_fifth_le_yNat,
      hrootTop.eventually (eventually_ge_atTop (3 : Real)),
      eventually_ge_atTop (1 : Nat)]
      with n hyNat hroot hn
  have hnOne : (1 : Real) <= (n : Real) := by
    exact_mod_cast hn
  have hdeltaTenth : deltaStar <= 1 / 10 := by
    linarith
  have hpowerDelta :
      (n : Real) ^ deltaStar <= (n : Real) ^ (1 / 10 : Real) :=
    Real.rpow_le_rpow_of_exponent_le hnOne hdeltaTenth
  have hcut :
      (tangentPaperExceptionalCutoff deltaStar n : Real) <
        (n : Real) ^ (1 / 10 : Real) + 1 := by
    calc
      (tangentPaperExceptionalCutoff deltaStar n : Real) <
          (n : Real) ^ deltaStar + 1 :=
        tangentPaperExceptionalCutoff_cast_lt_add_one deltaStar n
      _ <= (n : Real) ^ (1 / 10 : Real) + 1 :=
        add_le_add hpowerDelta le_rfl
  have hrootSq :
      ((n : Real) ^ (1 / 10 : Real)) ^ 2 =
        (n : Real) ^ (1 / 5 : Real) := by
    calc
      ((n : Real) ^ (1 / 10 : Real)) ^ 2 =
          (n : Real) ^ ((1 / 10 : Real) * (2 : Nat)) :=
        (Real.rpow_mul_natCast
          (Nat.cast_nonneg n) (1 / 10 : Real) 2).symm
      _ = (n : Real) ^ (1 / 5 : Real) := by norm_num
  have hreal :
      ((2 * tangentPaperExceptionalCutoff deltaStar n : Nat) : Real) <=
        (yNat n : Real) := by
    apply le_of_lt
    calc
      ((2 * tangentPaperExceptionalCutoff deltaStar n : Nat) : Real) =
          2 * (tangentPaperExceptionalCutoff deltaStar n : Real) := by
        norm_num
      _ < 2 * ((n : Real) ^ (1 / 10 : Real) + 1) :=
        mul_lt_mul_of_pos_left hcut (by norm_num)
      _ <= ((n : Real) ^ (1 / 10 : Real)) ^ 2 := by
        nlinarith
      _ = (n : Real) ^ (1 / 5 : Real) := hrootSq
      _ <= (yNat n : Real) := hyNat
  exact_mod_cast hreal

/-! ## Uniform padded coordinates on the deep prefix -/

/-- A positive smooth core at most half of the natural exceptional cutoff
has its frozen point inside the common padded endpoint chamber. -/
theorem roughCanonicalFourFiveFrozenCoordinate_mem_padded_of_deepCore
    {n b : Nat} {deltaStar : Real}
    (hn : 1 <= n) (hdelta : 0 <= deltaStar)
    (hcommon :
      RoughCanonicalExceptionalCommonEndpointGeometry n deltaStar)
    (hb :
      b ∈ Finset.Icc 1
        (tangentPaperExceptionalCutoff deltaStar n / 2)) :
    roughCanonicalFourFiveFrozenCoordinate n b ∈
      Set.Icc ((41 : Real) / 10) ((47 : Real) / 10) := by
  have hbData := Finset.mem_Icc.mp hb
  have hbPosNat : 0 < b := by omega
  have hbPos : (0 : Real) < (b : Real) := by
    exact_mod_cast hbPosNat
  have hbOne : (1 : Real) <= (b : Real) := by
    exact_mod_cast hbData.1
  have hnPos : (0 : Real) < (n : Real) := by
    exact_mod_cast (show 0 < n by omega)
  have hnOne : (1 : Real) <= (n : Real) := by
    exact_mod_cast hn
  have hpowerPos : 0 < (n : Real) ^ deltaStar :=
    Real.rpow_pos_of_pos hnPos deltaStar
  have hpowerOne : 1 <= (n : Real) ^ deltaStar :=
    Real.one_le_rpow hnOne hdelta
  have hbTwoNat :
      2 * b <= tangentPaperExceptionalCutoff deltaStar n := by
    omega
  have hbTwo :
      (2 : Real) * (b : Real) <=
        (tangentPaperExceptionalCutoff deltaStar n : Real) := by
    exact_mod_cast hbTwoNat
  have hcutUpper :=
    tangentPaperExceptionalCutoff_cast_lt_add_one deltaStar n
  have hbPower : (b : Real) <= (n : Real) ^ deltaStar := by
    nlinarith
  have hfloor :
      (roughCanonicalRealExceptionalRoughCutoff n deltaStar : Real) <=
        2 * (n : Real) / (n : Real) ^ deltaStar := by
    unfold roughCanonicalRealExceptionalRoughCutoff
    exact
      Nat.floor_le
        (div_nonneg (by positivity) hpowerPos.le)
  have hlower :
      (roughCanonicalRealExceptionalRoughCutoff n deltaStar : Real) <=
        2 * (n : Real) / (b : Real) := by
    exact hfloor.trans
      (div_le_div_of_nonneg_left (by positivity) hbPos hbPower)
  have hdivTwo :
      2 * (n : Real) / (b : Real) <= 2 * (n : Real) := by
    have h :=
      div_le_div_of_nonneg_left
        (show 0 <= 2 * (n : Real) by positivity)
        (by norm_num : (0 : Real) < 1) hbOne
    simpa only [div_one] using h
  have hupper :
      2 * (n : Real) / (b : Real) <= ((3 * n : Nat) : Real) := by
    calc
      2 * (n : Real) / (b : Real) <= 2 * (n : Real) := hdivTwo
      _ <= 3 * (n : Real) := by
        nlinarith [show (0 : Real) <= (n : Real) from Nat.cast_nonneg n]
      _ = ((3 * n : Nat) : Real) := by norm_num
  have hrange :=
    hcommon.padded_log_range
      (2 * (n : Real) / (b : Real)) ⟨hlower, hupper⟩
  simpa only [roughCanonicalFourFiveFrozenCoordinate] using hrange

/-- Eventual simultaneous padded-coordinate geometry for every smooth core
in the complete deep prefix. -/
theorem
    eventually_roughCanonicalFourFiveFrozenCoordinate_mem_padded_of_deepCore
    {deltaStar : Real} (hdelta : 0 <= deltaStar)
    (hdeltaUpper : deltaStar < 1 / 18) :
    ∀ᶠ n : Nat in atTop, ∀ b : Nat,
      b ∈ Finset.Icc 1
          (tangentPaperExceptionalCutoff deltaStar n / 2) ->
        roughCanonicalFourFiveFrozenCoordinate n b ∈
          Set.Icc ((41 : Real) / 10) ((47 : Real) / 10) := by
  filter_upwards [
      eventually_roughCanonicalExceptionalCommonEndpointGeometry
        hdelta hdeltaUpper,
      eventually_ge_atTop (1 : Nat)]
      with n hcommon hn
  intro b hb
  exact
    roughCanonicalFourFiveFrozenCoordinate_mem_padded_of_deepCore
      hn hdelta hcommon hb

/-! ## Routine chamber fields and the combined precursor -/

/-- The five scalar fields of the four/five chamber input which do not
depend on any of the six interval estimates. -/
structure RoughCanonicalSignedExceptionalFourFiveScalarBoundsAt
    (W n : Nat) (deltaStar : Real) : Prop where
  n_two : 2 <= n
  head_le_yNat : W <= yNat n
  core_cutoff_le_yNat :
    2 * tangentPaperExceptionalCutoff deltaStar n <= yNat n
  log_scale_one : 1 <= L n
  log_yNat_one : 1 <= Real.log (yNat n : Real)

/-- All five routine scalar chamber fields hold simultaneously eventually. -/
theorem
    eventually_roughCanonicalSignedExceptionalFourFiveScalarBoundsAt
    (W : Nat) {deltaStar : Real}
    (hdeltaUpper : deltaStar < 1 / 18) :
    ∀ᶠ n : Nat in atTop,
      RoughCanonicalSignedExceptionalFourFiveScalarBoundsAt
        W n deltaStar := by
  have hLTop : Tendsto L atTop atTop := by
    simpa only [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [
      eventually_ge_atTop (2 : Nat),
      roughCanonicalExceptional_yNat_tendsto_atTop.eventually
        (eventually_ge_atTop W),
      eventually_two_mul_tangentPaperExceptionalCutoff_le_yNat
        hdeltaUpper,
      hLTop.eventually (eventually_ge_atTop (1 : Real)),
      roughCanonicalExceptional_log_yNat_tendsto_atTop.eventually
        (eventually_ge_atTop (1 : Real))]
      with n hn hhead hcut hL hlogY
  exact
    { n_two := hn
      head_le_yNat := hhead
      core_cutoff_le_yNat := hcut
      log_scale_one := hL
      log_yNat_one := hlogY }

/-- The scalar fields together with the stronger all-deep-core coordinate
statement form the geometry precursor to the six interval estimates. -/
structure RoughCanonicalSignedExceptionalFourFiveGeometryPrecursorAt
    (W n : Nat) (deltaStar : Real) : Prop where
  scalar_bounds :
    RoughCanonicalSignedExceptionalFourFiveScalarBoundsAt W n deltaStar
  deep_coordinates :
    ∀ b ∈ Finset.Icc 1
        (tangentPaperExceptionalCutoff deltaStar n / 2),
      roughCanonicalFourFiveFrozenCoordinate n b ∈
        Set.Icc ((41 : Real) / 10) ((47 : Real) / 10)

/-- The stronger all-core coordinate statement directly supplies the
prime-power coordinate field used by the chamber input. -/
theorem
    RoughCanonicalSignedExceptionalFourFiveGeometryPrecursorAt.variation_coordinates
    {W n : Nat} {deltaStar : Real}
    (h :
      RoughCanonicalSignedExceptionalFourFiveGeometryPrecursorAt
        W n deltaStar) :
    ∀ p : Nat, p.Prime -> W < p ->
      ∀ k ∈ positiveExponents
          (tangentPaperExceptionalCutoff deltaStar n / 2),
        ∀ m ∈ Finset.Icc 1
            ((tangentPaperExceptionalCutoff deltaStar n / 2) / p ^ k),
          roughCanonicalFourFiveFrozenCoordinate n (p ^ k * m) ∈
            Set.Icc ((41 : Real) / 10) ((47 : Real) / 10) := by
  intro p hp _hpW k _hk m hm
  have hmData := Finset.mem_Icc.mp hm
  have hpower : 0 < p ^ k := pow_pos hp.pos k
  have hproductUpper :
      p ^ k * m <= tangentPaperExceptionalCutoff deltaStar n / 2 := by
    simpa only [Nat.mul_comm] using
      (Nat.le_div_iff_mul_le hpower).mp hmData.2
  exact
    h.deep_coordinates (p ^ k * m)
      (Finset.mem_Icc.mpr
        ⟨mul_pos hpower hmData.1, hproductUpper⟩)

/-- The complete elementary geometry precursor holds eventually. -/
theorem
    eventually_roughCanonicalSignedExceptionalFourFiveGeometryPrecursorAt
    (W : Nat) {deltaStar : Real}
    (hdelta : 0 <= deltaStar)
    (hdeltaUpper : deltaStar < 1 / 18) :
    ∀ᶠ n : Nat in atTop,
      RoughCanonicalSignedExceptionalFourFiveGeometryPrecursorAt
        W n deltaStar := by
  filter_upwards [
      eventually_roughCanonicalSignedExceptionalFourFiveScalarBoundsAt
        W hdeltaUpper,
      eventually_roughCanonicalFourFiveFrozenCoordinate_mem_padded_of_deepCore
        hdelta hdeltaUpper]
      with n hscalar hcoordinates
  exact
    { scalar_bounds := hscalar
      deep_coordinates := hcoordinates }

end BankPaperRealization

end

end Erdos390.WholePaper
