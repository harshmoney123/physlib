/-
Copyright (c) 2026 Harsha Vankayalapati. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harsha Vankayalapati
-/
module

public import PhyslibAlpha.Relativity.General.EnergyConditions
public import PhyslibAlpha.Relativity.General.MorrisThorne.Einstein

/-!

# The null energy condition is violated at a Morris-Thorne throat

The matter required by Einstein's equations to support a Morris-Thorne wormhole violates the null
energy condition at the throat.

## i. Overview

By Einstein's equations `G_{ab} = 8 π T_{ab}` (units `G = c = 1`), a Morris-Thorne wormhole with
zero redshift function and shape function `b` is supported by the stress-energy tensor
`T_{ab} = G_{ab} / (8 π)` (`requiredStressEnergy`). Its energy density, measured by the static
observers `∂_t`, is `ρ = T_tt = b' / (8 π r²)` and its radial pressure is
`p_r = T_rr / g_rr = - b / (8 π r³)`, so that
`ρ + p_r = (r b' - b) / (8 π r³)` (`morrisThorne_density_add_radialPressure`).

For `k = ∂_t + √(1 - b/r) ∂_r`, which is null, `T k k = ρ + p_r`
(`requiredStressEnergy_morrisThorne_null`). Hence the null energy condition fails at every point
with `r b'(r) < b(r)` (`not_nullEnergyCondition_morrisThorne`).

A throat is a radius `r₀ > 0` with `b(r₀) = r₀`, and flaring out means `b'(r₀) < 1`. At the throat
itself the coordinate `r` is singular, so the statement is a limit: as `r → r₀` from outside,
`ρ + p_r → (b'(r₀) - 1) / (8 π r₀²) < 0`
(`tendsto_density_add_radialPressure_throat`), the region `r > b(r)` contains the points just
outside the throat, and at all of them the null energy condition fails
(`not_nullEnergyCondition_morrisThorne_near_throat`).

## ii. Key results

- `requiredStressEnergy` : the stress-energy tensor `G_{ab} / (8 π)` required by Einstein's
  equations.
- `morrisThorne_density_add_radialPressure` : `ρ + p_r = (r b' - b) / (8 π r³)`.
- `not_nullEnergyCondition_morrisThorne` : the null energy condition fails where `r b' < b`.
- `tendsto_density_add_radialPressure_throat` : the limit of `ρ + p_r` at the throat is negative.
- `not_nullEnergyCondition_morrisThorne_near_throat` : the null energy condition is violated at
  all points of the region just outside a flared-out throat.

## iii. Table of contents

- A. The matter required by Einstein's equations
- B. Energy density and radial pressure
- C. A null vector
- D. Violation of the null energy condition
- E. The throat

## iv. References

- M. S. Morris and K. S. Thorne, *Wormholes in spacetime and their use for interstellar travel:
  A tool for teaching general relativity*, Am. J. Phys. 56, 395 (1988).

-/

@[expose] public section

noncomputable section

namespace GeneralRelativity

open Real Filter Topology
open scoped ContDiff

/-!

## A. The matter required by Einstein's equations

-/

/-- The stress-energy tensor `T_{ab} = G_{ab} / (8 π)` required by Einstein's equations
`G_{ab} = 8 π T_{ab}` for the metric field `g`, in units `G = c = 1`. -/
def requiredStressEnergy (g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ) (x : Fin 4 → ℝ) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun a b => einstein g x a b / (8 * π)

/-- The energy density `ρ = T_tt` seen by the static observers `∂_t` of the matter required by
Einstein's equations. -/
def requiredDensity (g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ) (x : Fin 4 → ℝ) : ℝ :=
  requiredStressEnergy g x 0 0

/-- The radial pressure `p_r = T_rr / g_rr` of the matter required by Einstein's equations. -/
def requiredRadialPressure (g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ) (x : Fin 4 → ℝ) : ℝ :=
  requiredStressEnergy g x 1 1 * (g x)⁻¹ 1 1

/-!

## B. Energy density and radial pressure

-/

section Pressure

variable {b : ℝ → ℝ} {x : Fin 4 → ℝ}

/-- The energy density of the matter required by a Morris-Thorne wormhole is `b' / (8 π r²)`. -/
lemma requiredDensity_morrisThorne (hb : ContDiff ℝ ∞ b) (hx : x ∈ morrisThorneDomain b) :
    requiredDensity (morrisThorneMetric b) x = deriv b (x 1) / (8 * π * x 1 ^ 2) := by
  have h1 := (morrisThorneDomain.pos hx).ne'
  simp only [requiredDensity, requiredStressEnergy, Matrix.of_apply, einstein_morrisThorne hb hx,
    morrisThorneEinstein, Matrix.diagonal_apply_eq]
  simp
  field_simp

/-- The radial pressure of the matter required by a Morris-Thorne wormhole is
`-b / (8 π r³)`. -/
lemma requiredRadialPressure_morrisThorne (hb : ContDiff ℝ ∞ b) (hx : x ∈ morrisThorneDomain b) :
    requiredRadialPressure (morrisThorneMetric b) x = -b (x 1) / (8 * π * x 1 ^ 3) := by
  have h1 := (morrisThorneDomain.pos hx).ne'
  have h2 := (morrisThorneDomain.sub_pos hx).ne'
  simp only [requiredRadialPressure, requiredStressEnergy, Matrix.of_apply,
    einstein_morrisThorne hb hx, morrisThorneMetric_inv hx, morrisThorneEinstein,
    Matrix.diagonal_apply_eq]
  simp
  field_simp

/-- `ρ + p_r = (r b' - b) / (8 π r³)` for the matter required by a Morris-Thorne wormhole. -/
lemma morrisThorne_density_add_radialPressure (hb : ContDiff ℝ ∞ b)
    (hx : x ∈ morrisThorneDomain b) :
    requiredDensity (morrisThorneMetric b) x + requiredRadialPressure (morrisThorneMetric b) x
      = (x 1 * deriv b (x 1) - b (x 1)) / (8 * π * x 1 ^ 3) := by
  have h1 := (morrisThorneDomain.pos hx).ne'
  rw [requiredDensity_morrisThorne hb hx, requiredRadialPressure_morrisThorne hb hx]
  field_simp
  ring

end Pressure

/-!

## C. A null vector

-/

section NullVector

variable {b : ℝ → ℝ} {x : Fin 4 → ℝ}

/-- The radially outgoing null vector `∂_t + √(1 - b/r) ∂_r`. -/
def morrisThorneNull (b : ℝ → ℝ) (x : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![1, √(1 - b (x 1) / x 1), 0, 0]

lemma toBilin'_diagonal_four (w : Fin 4 → ℝ) (v u : Fin 4 → ℝ) :
    Matrix.toBilin' (Matrix.diagonal w) v u
      = w 0 * (v 0 * u 0) + w 1 * (v 1 * u 1) + w 2 * (v 2 * u 2) + w 3 * (v 3 * u 3) := by
  simp [Matrix.toBilin'_apply', dotProduct, Matrix.mulVec_diagonal, Fin.sum_univ_four]
  ring

lemma isNull_morrisThorneNull (hx : x ∈ morrisThorneDomain b) :
    IsNull (Matrix.toBilin' (morrisThorneMetric b x)) (morrisThorneNull b x) := by
  have h2 := (morrisThorneDomain.one_sub_pos hx)
  refine ⟨?_, fun h => ?_⟩
  · have hs := Real.mul_self_sqrt h2.le
    rw [morrisThorneMetric, toBilin'_diagonal_four]
    simp [morrisThorneNull, hs, h2.ne']
  · have := congrFun h 0
    simp [morrisThorneNull] at this

/-- The stress-energy tensor required by a Morris-Thorne wormhole evaluated on the null vector
`morrisThorneNull` is `ρ + p_r`. -/
lemma requiredStressEnergy_morrisThorne_null (hb : ContDiff ℝ ∞ b)
    (hx : x ∈ morrisThorneDomain b) :
    Matrix.toBilin' (requiredStressEnergy (morrisThorneMetric b) x)
      (morrisThorneNull b x) (morrisThorneNull b x)
      = requiredDensity (morrisThorneMetric b) x
        + requiredRadialPressure (morrisThorneMetric b) x := by
  have h1 := (morrisThorneDomain.pos hx).ne'
  have h2 := (morrisThorneDomain.one_sub_pos hx)
  have h3 := (morrisThorneDomain.sub_pos hx).ne'
  have hT : requiredStressEnergy (morrisThorneMetric b) x
      = Matrix.diagonal fun i => requiredStressEnergy (morrisThorneMetric b) x i i := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · simp only [requiredStressEnergy, Matrix.of_apply, einstein_morrisThorne hb hx,
        morrisThorneEinstein, Matrix.diagonal_apply_ne _ hij]
      simp
  rw [hT, toBilin'_diagonal_four]
  simp only [morrisThorneNull, requiredRadialPressure, morrisThorneMetric_inv hx, requiredDensity]
  have hs := Real.mul_self_sqrt h2.le
  simp [hs]

end NullVector

/-!

## D. Violation of the null energy condition

-/

section Violation

variable {b : ℝ → ℝ} {x : Fin 4 → ℝ}

/-- The null energy condition fails for the matter required by a Morris-Thorne wormhole at every
point of the region where `r b'(r) < b(r)`. -/
lemma not_nullEnergyCondition_morrisThorne (hb : ContDiff ℝ ∞ b) (hx : x ∈ morrisThorneDomain b)
    (h : x 1 * deriv b (x 1) < b (x 1)) :
    ¬ NullEnergyCondition (Matrix.toBilin' (morrisThorneMetric b x))
      (Matrix.toBilin' (requiredStressEnergy (morrisThorneMetric b) x)) := by
  intro hnec
  have := hnec _ (isNull_morrisThorneNull hx)
  rw [requiredStressEnergy_morrisThorne_null hb hx, morrisThorne_density_add_radialPressure hb hx]
    at this
  have h1 := morrisThorneDomain.pos hx
  have : (x 1 * deriv b (x 1) - b (x 1)) / (8 * π * x 1 ^ 3) < 0 :=
    div_neg_of_neg_of_pos (by linarith) (by positivity)
  linarith

end Violation

/-!

## E. The throat

-/

section Throat

variable {b : ℝ → ℝ} {r₀ : ℝ}

/-- Flaring out at a throat: just outside the throat, `b(r) < r`. -/
lemma eventually_lt_nhdsGT_throat (hb : ContDiff ℝ ∞ b) (hthroat : b r₀ = r₀)
    (hflare : deriv b r₀ < 1) : ∀ᶠ r in 𝓝[>] r₀, b r < r := by
  have hd : HasDerivAt (fun r => r - b r) (1 - deriv b r₀) r₀ :=
    (hasDerivAt_id' r₀).sub ((hb.differentiable (by simp)) r₀).hasDerivAt
  have hs := (hasDerivAt_iff_tendsto_slope.mp hd).mono_left (nhdsGT_le_nhdsNE r₀)
  have hpos : ∀ᶠ r in 𝓝[>] r₀, 0 < slope (fun r => r - b r) r₀ r :=
    hs.eventually (lt_mem_nhds (by linarith))
  filter_upwards [hpos, self_mem_nhdsWithin] with r hr hr'
  have hr' : 0 < r - r₀ := sub_pos.mpr hr'
  rw [slope_def_field] at hr
  simp only [hthroat, sub_self, sub_zero] at hr
  have := (div_pos_iff_of_pos_right hr').mp hr
  linarith

/-- At a flared-out throat the quantity `r b'(r) - b(r)` is negative just outside the throat. -/
lemma eventually_mul_deriv_lt_nhdsGT_throat (hb : ContDiff ℝ ∞ b) (hr₀ : 0 < r₀)
    (hthroat : b r₀ = r₀) (hflare : deriv b r₀ < 1) :
    ∀ᶠ r in 𝓝[>] r₀, r * deriv b r < b r := by
  obtain ⟨hd, hd'⟩ := contDiff_infty_iff_deriv.mp hb
  have hc : ContinuousAt (fun r => r * deriv b r - b r) r₀ :=
    (continuous_id.mul hd'.continuous).continuousAt.sub hb.continuous.continuousAt
  have hneg : (fun r => r * deriv b r - b r) r₀ < 0 := by
    simp only [hthroat]
    nlinarith
  have := (hc.eventually_lt continuousAt_const hneg).filter_mono (nhdsWithin_le_nhds (s := Set.Ioi r₀))
  filter_upwards [this] with r hr
  linarith

/-- The limit of `ρ + p_r` at a flared-out throat is `(b'(r₀) - 1) / (8 π r₀²)`, which is
negative. -/
lemma tendsto_density_add_radialPressure_throat (hb : ContDiff ℝ ∞ b) (hr₀ : 0 < r₀)
    (hthroat : b r₀ = r₀) :
    Tendsto (fun r => (r * deriv b r - b r) / (8 * π * r ^ 3)) (𝓝[>] r₀)
      (𝓝 ((deriv b r₀ - 1) / (8 * π * r₀ ^ 2))) := by
  obtain ⟨hd, hd'⟩ := contDiff_infty_iff_deriv.mp hb
  have hc : ContinuousAt (fun r => (r * deriv b r - b r) / (8 * π * r ^ 3)) r₀ := by
    refine ContinuousAt.div
      ((continuous_id.mul hd'.continuous).continuousAt.sub hb.continuous.continuousAt)
      (by fun_prop) (by positivity)
  have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi r₀))
  convert this using 2
  simp only [hthroat]
  field_simp

/-- The limit of `ρ + p_r` at a flared-out throat is negative. -/
lemma limit_density_add_radialPressure_throat_neg (hr₀ : 0 < r₀) (hflare : deriv b r₀ < 1) :
    (deriv b r₀ - 1) / (8 * π * r₀ ^ 2) < 0 :=
  div_neg_of_neg_of_pos (by linarith) (by positivity)

/-- The null energy condition is violated by the matter required by a Morris-Thorne wormhole at
all points just outside a flared-out throat (`b(r₀) = r₀`, `b'(r₀) < 1`): there is `ε > 0` such
that every point of the wormhole with `r₀ < r < r₀ + ε` lies in the region `b(r) < r` and has a
null vector `k` with `T k k < 0`. -/
theorem not_nullEnergyCondition_morrisThorne_near_throat (hb : ContDiff ℝ ∞ b) (hr₀ : 0 < r₀)
    (hthroat : b r₀ = r₀) (hflare : deriv b r₀ < 1) :
    ∀ᶠ r in 𝓝[>] r₀, ∀ x : Fin 4 → ℝ, x 1 = r → 0 < x 2 → x 2 < π →
      x ∈ morrisThorneDomain b ∧
        ¬ NullEnergyCondition (Matrix.toBilin' (morrisThorneMetric b x))
          (Matrix.toBilin' (requiredStressEnergy (morrisThorneMetric b) x)) := by
  filter_upwards [eventually_lt_nhdsGT_throat hb hthroat hflare,
    eventually_mul_deriv_lt_nhdsGT_throat hb hr₀ hthroat hflare, self_mem_nhdsWithin]
    with r hlt hmul hr
  intro x hx1 hx2 hx2'
  subst hx1
  have hmem : x ∈ morrisThorneDomain b := ⟨lt_trans hr₀ hr, hlt, hx2, hx2'⟩
  exact ⟨hmem, not_nullEnergyCondition_morrisThorne hb hmem hmul⟩

end Throat

end GeneralRelativity
