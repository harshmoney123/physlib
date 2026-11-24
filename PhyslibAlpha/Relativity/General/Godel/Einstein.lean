/-
Copyright (c) 2026 Harsha Vankayalapati. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harsha Vankayalapati
-/
module

public import PhyslibAlpha.Relativity.General.Godel.Christoffel

/-!

# The Gödel metric solves Einstein's equations with dust and a cosmological constant

The Ricci tensor of the Gödel metric is `R_{ab} = 4 u_a u_b`, where `u^a = ∂_t` is the unit
timelike dust four-velocity, so Gödel's universe is a solution of the Einstein equations with
pressureless dust and a negative cosmological constant.

## i. Overview

The Christoffel symbols of the Gödel metric (`christoffel_godelMetric`) depend only on `r`, so
each component of the Ricci tensor `R_{bd} = ∑_a R^a_{bad}` is an explicit function of `sinh r` and
`cosh r`. We first rewrite `ricci godelMetric` in terms of the closed forms of the Christoffel
symbols and their derivatives (`ricci_godelMetric_expr`), and then check the sixteen components
one at a time (`ricci_godelMetric`).

The dust four-velocity is `u^a = δ^a_t`, which is a unit timelike vector because `g_{tt} = -1`;
its lowering is `u_a = g_{a t}` (`godelVelocityLower`). We find `R_{ab} = 4 u_a u_b`
(`ricci_godelMetric`), hence the Ricci scalar is `R = -4` (`ricciScalar_godelMetric`) and the
Einstein tensor is `G_{ab} = 4 u_a u_b + 2 g_{ab}` (`einstein_godelMetric`).

In units `8 π G = 1`, Einstein's equations with dust of density `ρ` and a cosmological constant
`Λ` read `G_{ab} + Λ g_{ab} = ρ u_a u_b`, or, in trace-reversed form,
`R_{ab} = ρ u_a u_b + (ρ / 2 + Λ) g_{ab}`. The Gödel metric solves them with `ρ = 4`
(`godelDensity`) and `Λ = -2` (`godelCosmologicalConstant`): see `einstein_add_cosmological_godel`
and `ricci_godel_dust_cosmological`. For a general length scale `a` one has `ρ = 1 / a²`
and `Λ = -1 / (2 a²)`; here `a = 1/2`.

## ii. Key results

- `ricci_godelMetric_expr` : the Ricci tensor in terms of the closed form Christoffel symbols.
- `ricci_godelMetric` : `R_{ab} = 4 u_a u_b`.
- `ricciScalar_godelMetric` : the Ricci scalar is `-4`.
- `einstein_godelMetric` : the Einstein tensor is `4 u_a u_b + 2 g_{ab}`.
- `einstein_add_cosmological_godel` : `G_{ab} + Λ g_{ab} = ρ u_a u_b` with `ρ = 4`, `Λ = -2`.
- `ricci_godel_dust_cosmological` : the trace-reversed form of the same equation.

## iii. Table of contents

- A. The dust four-velocity
- B. The Ricci tensor
- C. Einstein's equations with dust and a cosmological constant

## iv. References

- K. Gödel, *An example of a new type of cosmological solutions of Einstein's field equations of
  gravitation*, Rev. Mod. Phys. 21, 447 (1949).
- S. W. Hawking and G. F. R. Ellis, *The Large Scale Structure of Space-Time*, Section 5.2.

-/

@[expose] public section

noncomputable section

namespace GeneralRelativity

open Real

/-!

## A. The dust four-velocity

-/

/-- The covariant dust four-velocity `u_a = g_{a t}` of the Gödel universe, the lowering of the
unit timelike vector `u^a = ∂_t`. -/
def godelVelocityLower (y : Fin 4 → ℝ) (a : Fin 4) : ℝ := godelMetric y a 0

/-- The dust four-velocity `∂_t` is a unit timelike vector: `g_{tt} = -1`. -/
lemma godelVelocityLower_apply_zero (y : Fin 4 → ℝ) : godelVelocityLower y 0 = -1 := by
  simp [godelVelocityLower, godelMetric, godelMetricR]

/-!

## B. The Ricci tensor

-/

lemma coordDeriv_christoffel_godelMetric {x : Fin 4 → ℝ} (hx : x ∈ godelDomain)
    (a b c e : Fin 4) : coordDeriv (fun y => christoffel godelMetric y a b c) x e
      = if e = 1 then godelGamma' a b c (x 1) else 0 := by
  have hr : 0 < x 1 := hx
  have hs : sinh (x 1) ≠ 0 := (sinh_pos_iff.2 hr).ne'
  have hc : cosh (x 1) ≠ 0 := (cosh_pos _).ne'
  have hcongr : (fun y => christoffel godelMetric y a b c)
      =ᶠ[nhds x] fun y => godelGamma a b c (y 1) := by
    filter_upwards [isOpen_godelDomain.mem_nhds hx] with y hy
    exact christoffel_godelMetric hy a b c
  have h := hasDerivAt_godelGamma hs hc a b c
  rw [coordDeriv_congr hcongr e, coordDeriv_comp_proj 1 h.differentiableAt, h.deriv]

/-- The Ricci tensor of the Gödel metric in terms of the closed forms of the Christoffel symbols
and their derivatives. -/
lemma ricci_godelMetric_expr {x : Fin 4 → ℝ} (hx : x ∈ godelDomain) (b d : Fin 4) :
    ricci godelMetric x b d = ∑ a, (
      (if a = 1 then godelGamma' a d b (x 1) else 0)
      - (if d = 1 then godelGamma' a a b (x 1) else 0)
      + ∑ e, (godelGamma a a e (x 1) * godelGamma e d b (x 1)
        - godelGamma a d e (x 1) * godelGamma e a b (x 1))) := by
  simp only [ricci, riemann, coordDeriv_christoffel_godelMetric hx, christoffel_godelMetric hx]

/-- The Ricci tensor of the Gödel metric is `R_{ab} = 4 u_a u_b`, where `u_a = g_{a t}` is the
dust four-velocity. -/
theorem ricci_godelMetric {x : Fin 4 → ℝ} (hx : x ∈ godelDomain) (b d : Fin 4) :
    ricci godelMetric x b d = 4 * godelVelocityLower x b * godelVelocityLower x d := by
  have hr : 0 < x 1 := hx
  have hs : sinh (x 1) ≠ 0 := (sinh_pos_iff.2 hr).ne'
  have hc : cosh (x 1) ≠ 0 := (cosh_pos _).ne'
  have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hcs := cosh_sq (x 1)
  rw [ricci_godelMetric_expr hx]
  fin_cases b <;> fin_cases d <;>
  simp [Fin.sum_univ_four, godelGamma, godelGamma', godelVelocityLower, godelMetric,
    godelMetricR]
  all_goals field_simp
  all_goals (simp only [h2, hcs]; ring1)

/-- The Ricci scalar of the Gödel metric is `-4`. -/
lemma ricciScalar_godelMetric {x : Fin 4 → ℝ} (hx : x ∈ godelDomain) :
    ricciScalar godelMetric x = -4 := by
  have hr : 0 < x 1 := hx
  have hs : sinh (x 1) ≠ 0 := (sinh_pos_iff.2 hr).ne'
  have hc : cosh (x 1) ≠ 0 := (cosh_pos _).ne'
  have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hcs := cosh_sq (x 1)
  simp only [ricciScalar, ricci_godelMetric hx, godelMetric_inv hx]
  simp [Fin.sum_univ_four, godelMetricInvR, godelVelocityLower, godelMetric, godelMetricR]
  field_simp
  simp only [h2, hcs]
  ring

/-- The Einstein tensor of the Gödel metric is `G_{ab} = 4 u_a u_b + 2 g_{ab}`. -/
lemma einstein_godelMetric {x : Fin 4 → ℝ} (hx : x ∈ godelDomain) (a b : Fin 4) :
    einstein godelMetric x a b
      = 4 * godelVelocityLower x a * godelVelocityLower x b + 2 * godelMetric x a b := by
  simp only [einstein, ricci_godelMetric hx, ricciScalar_godelMetric hx]
  ring

/-!

## C. Einstein's equations with dust and a cosmological constant

-/

/-- The dust density `ρ = 4` of the Gödel universe with length scale `a = 1/2`, in units
`8 π G = 1`. -/
def godelDensity : ℝ := 4

/-- The cosmological constant `Λ = -2` of the Gödel universe with length scale `a = 1/2`. -/
def godelCosmologicalConstant : ℝ := -2

/-- The Gödel metric solves Einstein's equations with pressureless dust and a cosmological
constant: `G_{ab} + Λ g_{ab} = ρ u_a u_b`. -/
theorem einstein_add_cosmological_godel {x : Fin 4 → ℝ} (hx : x ∈ godelDomain) (a b : Fin 4) :
    einstein godelMetric x a b + godelCosmologicalConstant * godelMetric x a b
      = godelDensity * godelVelocityLower x a * godelVelocityLower x b := by
  rw [einstein_godelMetric hx]
  simp only [godelCosmologicalConstant, godelDensity]
  ring

/-- The trace-reversed form of Einstein's equations with dust and a cosmological constant:
`R_{ab} = ρ u_a u_b + (ρ / 2 + Λ) g_{ab}`. -/
theorem ricci_godel_dust_cosmological {x : Fin 4 → ℝ} (hx : x ∈ godelDomain) (a b : Fin 4) :
    ricci godelMetric x a b = godelDensity * godelVelocityLower x a * godelVelocityLower x b
      + (godelDensity / 2 + godelCosmologicalConstant) * godelMetric x a b := by
  rw [ricci_godelMetric hx]
  simp only [godelCosmologicalConstant, godelDensity]
  ring

end GeneralRelativity
