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

Throughout, `G : ℝ` is Newton's constant and `c : SpeedOfLight` is the speed of light; take
`c = 1` for units in which it is one. The metric has the signature `(+,-,-,-)`.

By Einstein's equations `G_{ab} = (8 π G / c⁴) T_{ab}`, a Morris-Thorne wormhole with zero
redshift function and shape function `b` is supported by the stress-energy tensor
`T_{ab} = c⁴ / (8 π G) G_{ab}` (`requiredStressEnergy`). As for a `CosmicFluid` in
`Physlib.Cosmology.FLRW.Basic`, we describe it by a mass density `ρ` and a pressure, for which
`ρ` and `p / c²` have the same dimension. The static observers have four-velocity `∂_t`,
normalised to `g(∂_t, ∂_t) = c²`, and measure the energy density `ρ c² = T_tt / c²`, so that
`ρ = c² b' / (8 π G r²)` (`requiredDensity_morrisThorne`). The radial pressure is the component
of `T` along the unit radial direction, `p_r = T_rr / (-g_rr) = - c⁴ b / (8 π G r³)`
(`requiredRadialPressure_morrisThorne`), so that
`ρ + p_r / c² = c² (r b' - b) / (8 π G r³)` (`morrisThorne_density_add_radialPressure`).

For `k = ∂_t + c √(1 - b/r) ∂_r`, which is null, `T k k = c⁴ (ρ + p_r / c²)`
(`requiredStressEnergy_morrisThorne_null`). Hence, for `G > 0`, at every point with
`r b'(r) < b(r)` we have `ρ + p_r / c² < 0` (`morrisThorne_density_add_radialPressure_neg`) and the
null energy condition fails (`not_nullEnergyCondition_morrisThorne`).

A throat is a radius `r₀ > 0` with `b(r₀) = r₀`, and flaring out means `b'(r₀) < 1`. At the throat
itself the coordinate `r` is singular, so the statement is a limit: as `r → r₀` from outside,
`ρ + p_r / c² → c² (b'(r₀) - 1) / (8 π G r₀²) < 0`
(`tendsto_density_add_radialPressure_throat`), the region `r > b(r)` contains the points just
outside the throat, and at all of them the null energy condition fails
(`not_nullEnergyCondition_morrisThorne_near_throat`).

## ii. Key results

- `requiredStressEnergy` : the stress-energy tensor `c⁴ / (8 π G) G_{ab}` required by Einstein's
  equations.
- `requiredDensity_morrisThorne`, `requiredRadialPressure_morrisThorne` : `ρ = c² b' / (8 π G r²)`
  and `p_r = - c⁴ b / (8 π G r³)`.
- `morrisThorne_density_add_radialPressure` : `ρ + p_r / c² = c² (r b' - b) / (8 π G r³)`.
- `not_nullEnergyCondition_morrisThorne` : the null energy condition fails where `r b' < b`.
- `tendsto_density_add_radialPressure_throat` : the limit of `ρ + p_r / c²` at the throat, which
  is negative.
- `not_nullEnergyCondition_morrisThorne_near_throat` : the null energy condition is violated at
  all points of the region just outside a flared-out throat.

## iii. Table of contents

- A. The matter required by Einstein's equations
- B. Mass density and radial pressure
- C. A null vector
- D. Violation of the null energy condition
- E. The throat

## iv. References

- M. S. Morris and K. S. Thorne, *Wormholes in spacetime and their use for interstellar travel:
  A tool for teaching general relativity*, Am. J. Phys. 56, 395 (1988) (in the opposite sign
  convention `(-,+,+,+)`; the density `ρ` and the radial tension `τ = - p_r` are given there with
  `G` and `c`).

-/

@[expose] public section

noncomputable section

namespace GeneralRelativity

open Real Filter Topology
open scoped ContDiff

/-!

## A. The matter required by Einstein's equations

-/

/-- The stress-energy tensor `T_{ab} = c⁴ / (8 π G) G_{ab}` required by Einstein's equations
`G_{ab} = (8 π G / c⁴) T_{ab}` for the metric field `g` of signature `(+,-,-,-)`.

- `G : ℝ` is Newton's constant.
- `c : SpeedOfLight` is the speed of light; take `c = 1` for units in which it is one. -/
def requiredStressEnergy (G : ℝ) (c : SpeedOfLight) (g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ)
    (x : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun a b => (c : ℝ) ^ 4 / (8 * π * G) * einstein g x a b

/-- The mass density `ρ = T_tt g^{tt} / c²` of the matter required by Einstein's equations, seen
by the static observers of a diagonal metric `g`: the energy density along their unit timelike
direction `∂_t / √g_tt` is `T_tt g^{tt} = ρ c²`. As for a `CosmicFluid`, `ρ` and `p / c²` have the
same dimension. When `g_tt = c²` the unit timelike direction is `∂_t / c` and `ρ = T_tt / c⁴`.

- `G : ℝ` is Newton's constant.
- `c : SpeedOfLight` is the speed of light; take `c = 1` for units in which it is one. -/
def requiredDensity (G : ℝ) (c : SpeedOfLight) (g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ)
    (x : Fin 4 → ℝ) : ℝ :=
  requiredStressEnergy G c g x 0 0 * (g x)⁻¹ 0 0 / (c : ℝ) ^ 2

/-- The radial pressure `p_r = -T_rr g^{rr}` of the matter required by Einstein's equations, for
a diagonal metric `g` of signature `(+,-,-,-)`: the component of `T` along the unit radial
direction `∂_r / √(-g_rr)`. The sign is there because `g_rr < 0`.

- `G : ℝ` is Newton's constant.
- `c : SpeedOfLight` is the speed of light; take `c = 1` for units in which it is one. -/
def requiredRadialPressure (G : ℝ) (c : SpeedOfLight)
    (g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ) (x : Fin 4 → ℝ) : ℝ :=
  -(requiredStressEnergy G c g x 1 1 * (g x)⁻¹ 1 1)

/-!

## B. Mass density and radial pressure

-/

section Pressure

variable {G : ℝ} {c : SpeedOfLight} {b : ℝ → ℝ} {x : Fin 4 → ℝ}

/-- The mass density of the matter required by a Morris-Thorne wormhole is
`c² b' / (8 π G r²)`. -/
lemma requiredDensity_morrisThorne (hb : ContDiff ℝ ∞ b) (hx : x ∈ morrisThorneDomain b) :
    requiredDensity G c (morrisThorneMetric c b) x
      = (c : ℝ) ^ 2 * deriv b (x 1) / (8 * π * G * x 1 ^ 2) := by
  have hc := c.val_ne_zero
  have h1 := (morrisThorneDomain.pos hx).ne'
  simp only [requiredDensity, requiredStressEnergy, Matrix.of_apply, einstein_morrisThorne hb hx,
    morrisThorneMetric_inv hx, morrisThorneEinstein, Matrix.diagonal_apply_eq]
  simp only [Fin.isValue, Matrix.cons_val_zero]
  field_simp

/-- The radial pressure of the matter required by a Morris-Thorne wormhole is
`- c⁴ b / (8 π G r³)`. -/
lemma requiredRadialPressure_morrisThorne (hb : ContDiff ℝ ∞ b) (hx : x ∈ morrisThorneDomain b) :
    requiredRadialPressure G c (morrisThorneMetric c b) x
      = -((c : ℝ) ^ 4 * b (x 1)) / (8 * π * G * x 1 ^ 3) := by
  have h1 := (morrisThorneDomain.pos hx).ne'
  have h2 := (morrisThorneDomain.sub_pos hx).ne'
  simp only [requiredRadialPressure, requiredStressEnergy, Matrix.of_apply,
    einstein_morrisThorne hb hx, morrisThorneMetric_inv hx, morrisThorneEinstein,
    Matrix.diagonal_apply_eq]
  simp only [Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero, Nat.succ_eq_add_one,
    Nat.reduceAdd, mul_inv_rev]
  field_simp

/-- `ρ + p_r / c² = c² (r b' - b) / (8 π G r³)` for the matter required by a Morris-Thorne
wormhole. -/
lemma morrisThorne_density_add_radialPressure (hb : ContDiff ℝ ∞ b)
    (hx : x ∈ morrisThorneDomain b) :
    requiredDensity G c (morrisThorneMetric c b) x
      + requiredRadialPressure G c (morrisThorneMetric c b) x / (c : ℝ) ^ 2
      = (c : ℝ) ^ 2 * (x 1 * deriv b (x 1) - b (x 1)) / (8 * π * G * x 1 ^ 3) := by
  have hc := c.val_ne_zero
  have h1 := (morrisThorneDomain.pos hx).ne'
  rw [requiredDensity_morrisThorne hb hx, requiredRadialPressure_morrisThorne hb hx]
  field_simp
  ring

/-- Where `r b'(r) < b(r)`, the matter required by a Morris-Thorne wormhole has
`ρ + p_r / c² < 0`. -/
lemma morrisThorne_density_add_radialPressure_neg (hG : 0 < G) (hb : ContDiff ℝ ∞ b)
    (hx : x ∈ morrisThorneDomain b) (h : x 1 * deriv b (x 1) < b (x 1)) :
    requiredDensity G c (morrisThorneMetric c b) x
      + requiredRadialPressure G c (morrisThorneMetric c b) x / (c : ℝ) ^ 2 < 0 := by
  have h1 := morrisThorneDomain.pos hx
  rw [morrisThorne_density_add_radialPressure hb hx]
  exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (pow_pos c.val_pos 2) (by linarith))
    (by positivity)

end Pressure

/-!

## C. A null vector

-/

section NullVector

variable {G : ℝ} {c : SpeedOfLight} {b : ℝ → ℝ} {x : Fin 4 → ℝ}

/-- The radially outgoing null vector `∂_t + c √(1 - b/r) ∂_r`: the sum of the four-velocity
`∂_t` of the static observers and `c` times the unit radial direction. -/
def morrisThorneNull (c : SpeedOfLight) (b : ℝ → ℝ) (x : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![1, (c : ℝ) * √(1 - b (x 1) / x 1), 0, 0]

lemma toBilin'_diagonal_four (w : Fin 4 → ℝ) (v u : Fin 4 → ℝ) :
    Matrix.toBilin' (Matrix.diagonal w) v u
      = w 0 * (v 0 * u 0) + w 1 * (v 1 * u 1) + w 2 * (v 2 * u 2) + w 3 * (v 3 * u 3) := by
  simp [Matrix.toBilin'_apply', dotProduct, Matrix.mulVec_diagonal, Fin.sum_univ_four]
  ring

lemma isNull_morrisThorneNull (hx : x ∈ morrisThorneDomain b) :
    IsNull (Matrix.toBilin' (morrisThorneMetric c b x)) (morrisThorneNull c b x) := by
  have h2 := (morrisThorneDomain.one_sub_pos hx)
  refine ⟨?_, fun h => ?_⟩
  · have hs := Real.mul_self_sqrt h2.le
    have hinv : (1 - b (x 1) / x 1)⁻¹ * (1 - b (x 1) / x 1) = 1 := inv_mul_cancel₀ h2.ne'
    rw [morrisThorneMetric, toBilin'_diagonal_four]
    simp only [morrisThorneNull, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, mul_zero, add_zero, mul_one]
    linear_combination (-(1 - b (x 1) / x 1)⁻¹ * (c : ℝ) ^ 2) * hs - (c : ℝ) ^ 2 * hinv
  · have := congrFun h 0
    simp [morrisThorneNull] at this

/-- The stress-energy tensor required by a Morris-Thorne wormhole evaluated on the null vector
`morrisThorneNull` is `c⁴ (ρ + p_r / c²)`. -/
lemma requiredStressEnergy_morrisThorne_null (hb : ContDiff ℝ ∞ b)
    (hx : x ∈ morrisThorneDomain b) :
    Matrix.toBilin' (requiredStressEnergy G c (morrisThorneMetric c b) x)
      (morrisThorneNull c b x) (morrisThorneNull c b x)
      = (c : ℝ) ^ 4 * (requiredDensity G c (morrisThorneMetric c b) x
        + requiredRadialPressure G c (morrisThorneMetric c b) x / (c : ℝ) ^ 2) := by
  have hc := c.val_ne_zero
  have h2 := (morrisThorneDomain.one_sub_pos hx)
  have hT : requiredStressEnergy G c (morrisThorneMetric c b) x
      = Matrix.diagonal fun i => requiredStressEnergy G c (morrisThorneMetric c b) x i i := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · simp only [requiredStressEnergy, Matrix.of_apply, einstein_morrisThorne hb hx,
        morrisThorneEinstein, Matrix.diagonal_apply_ne _ hij]
      simp
  rw [hT, toBilin'_diagonal_four]
  simp only [morrisThorneNull, requiredRadialPressure, morrisThorneMetric_inv hx, requiredDensity]
  have hs := Real.mul_self_sqrt h2.le
  have hcc : ∀ A B : ℝ, (c : ℝ) ^ 4 * (A * ((c : ℝ) ^ 2)⁻¹ / (c : ℝ) ^ 2 + B / (c : ℝ) ^ 2)
      = A + (c : ℝ) ^ 2 * B := fun A B => by field_simp
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    Matrix.diagonal_apply_eq, mul_zero, add_zero, mul_one, hcc]
  linear_combination (c : ℝ) ^ 2 * requiredStressEnergy G c (morrisThorneMetric c b) x 1 1 * hs

end NullVector

/-!

## D. Violation of the null energy condition

-/

section Violation

variable {G : ℝ} {c : SpeedOfLight} {b : ℝ → ℝ} {x : Fin 4 → ℝ}

/-- The null energy condition fails for the matter required by a Morris-Thorne wormhole at every
point of the region where `r b'(r) < b(r)`. -/
lemma not_nullEnergyCondition_morrisThorne (hG : 0 < G) (hb : ContDiff ℝ ∞ b)
    (hx : x ∈ morrisThorneDomain b) (h : x 1 * deriv b (x 1) < b (x 1)) :
    ¬ NullEnergyCondition (Matrix.toBilin' (morrisThorneMetric c b x))
      (Matrix.toBilin' (requiredStressEnergy G c (morrisThorneMetric c b) x)) := by
  intro hnec
  have := hnec _ (isNull_morrisThorneNull hx)
  rw [requiredStressEnergy_morrisThorne_null hb hx] at this
  have hneg := morrisThorne_density_add_radialPressure_neg (c := c) hG hb hx h
  nlinarith [pow_pos c.val_pos 4]

end Violation

/-!

## E. The throat

-/

section Throat

variable {G : ℝ} {c : SpeedOfLight} {b : ℝ → ℝ} {r₀ : ℝ}

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
  have := (hc.eventually_lt continuousAt_const hneg).filter_mono
    (nhdsWithin_le_nhds (s := Set.Ioi r₀))
  filter_upwards [this] with r hr
  linarith

/-- The limit of `ρ + p_r / c²` at a flared-out throat is `c² (b'(r₀) - 1) / (8 π G r₀²)`, which
is negative.

- `G : ℝ` is Newton's constant.
- `c : SpeedOfLight` is the speed of light; take `c = 1` for units in which it is one. -/
lemma tendsto_density_add_radialPressure_throat (G : ℝ) (c : SpeedOfLight) (hb : ContDiff ℝ ∞ b)
    (hr₀ : 0 < r₀) (hthroat : b r₀ = r₀) :
    Tendsto (fun r => (c : ℝ) ^ 2 * (r * deriv b r - b r) / (8 * π * G * r ^ 3)) (𝓝[>] r₀)
      (𝓝 ((c : ℝ) ^ 2 * (deriv b r₀ - 1) / (8 * π * G * r₀ ^ 2))) := by
  obtain ⟨hd, hd'⟩ := contDiff_infty_iff_deriv.mp hb
  have hc : ContinuousAt
      (fun r => (c : ℝ) ^ 2 / (8 * π * G) * ((r * deriv b r - b r) / r ^ 3)) r₀ :=
    continuousAt_const.mul (ContinuousAt.div
      ((continuous_id.mul hd'.continuous).continuousAt.sub hb.continuous.continuousAt)
      (by fun_prop) (by positivity))
  have hlim : (r₀ * deriv b r₀ - b r₀) / r₀ ^ 3 = (deriv b r₀ - 1) / r₀ ^ 2 := by
    rw [hthroat]
    field_simp
  have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi r₀))
  rw [hlim] at this
  convert this using 2 <;> ring

/-- The limit of `ρ + p_r / c²` at a flared-out throat is negative. -/
lemma limit_density_add_radialPressure_throat_neg (c : SpeedOfLight) (hG : 0 < G) (hr₀ : 0 < r₀)
    (hflare : deriv b r₀ < 1) : (c : ℝ) ^ 2 * (deriv b r₀ - 1) / (8 * π * G * r₀ ^ 2) < 0 :=
  div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (pow_pos c.val_pos 2) (by linarith))
    (by positivity)

/-- The null energy condition is violated by the matter required by a Morris-Thorne wormhole at
all points just outside a flared-out throat (`b(r₀) = r₀`, `b'(r₀) < 1`): there is `ε > 0` such
that every point of the wormhole with `r₀ < r < r₀ + ε` lies in the region `b(r) < r` and has a
null vector `k` with `T k k < 0`. Here `T_{ab} = c⁴ / (8 π G) G_{ab}`, `G : ℝ` is Newton's
constant, with `0 < G`, and `c : SpeedOfLight` is the speed of light. -/
theorem not_nullEnergyCondition_morrisThorne_near_throat (hG : 0 < G) (hb : ContDiff ℝ ∞ b)
    (hr₀ : 0 < r₀) (hthroat : b r₀ = r₀) (hflare : deriv b r₀ < 1) :
    ∀ᶠ r in 𝓝[>] r₀, ∀ x : Fin 4 → ℝ, x 1 = r → 0 < x 2 → x 2 < π →
      x ∈ morrisThorneDomain b ∧
        ¬ NullEnergyCondition (Matrix.toBilin' (morrisThorneMetric c b x))
          (Matrix.toBilin' (requiredStressEnergy G c (morrisThorneMetric c b) x)) := by
  filter_upwards [eventually_lt_nhdsGT_throat hb hthroat hflare,
    eventually_mul_deriv_lt_nhdsGT_throat hb hr₀ hthroat hflare, self_mem_nhdsWithin]
    with r hlt hmul hr
  intro x hx1 hx2 hx2'
  subst hx1
  have hmem : x ∈ morrisThorneDomain b := ⟨lt_trans hr₀ hr, hlt, hx2, hx2'⟩
  exact ⟨hmem, not_nullEnergyCondition_morrisThorne hG hb hmem hmul⟩

end Throat

end GeneralRelativity
