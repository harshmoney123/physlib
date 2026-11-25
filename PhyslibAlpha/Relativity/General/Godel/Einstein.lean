/-
Copyright (c) 2026 Harsha Vankayalapati. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harsha Vankayalapati
-/
module

public import PhyslibAlpha.Relativity.General.Godel.Christoffel
public import PhyslibAlpha.Relativity.General.PerfectFluidEnergyConditions

/-!

# The Gödel metric solves Einstein's equations with dust and a cosmological constant

The Ricci tensor of the Gödel metric is `R_{ab} = u_a u_b / (a² c²)`, where `u^a = ∂_t` is the
dust four-velocity, so Gödel's universe is a solution of the Einstein equations with pressureless
dust and a negative cosmological constant.

## i. Overview

The Christoffel symbols of the Gödel metric (`christoffel_godelMetric`) depend only on `r`, so
each component of the Ricci tensor `R_{bd} = ∑_a R^a_{bad}` is an explicit function of `sinh r` and
`cosh r`. We first rewrite `ricci (godelMetric a c)` in terms of the closed forms of the
Christoffel symbols and their derivatives (`ricci_godelMetric_expr`), and then check the sixteen
components one at a time (`ricci_godelMetric`).

The dust four-velocity is `u^a = δ^a_t`, normalised to `g(u, u) = g_{tt} = c²`; its lowering is
`u_a = g_{a t}` (`godelVelocityLower`). We find `R_{ab} = u_a u_b / (a² c²)`
(`ricci_godelMetric`), hence the Ricci scalar is `R = 1 / a²` (`ricciScalar_godelMetric`) and the
Einstein tensor is `G_{ab} = u_a u_b / (a² c²) - g_{ab} / (2 a²)` (`einstein_godelMetric`).

In the signature `(+,-,-,-)`, Einstein's equations with dust of mass density `ρ` and a
cosmological constant `Λ` read `G_{ab} - Λ g_{ab} = (8 π G / c⁴) ρ u_a u_b`, with `G` Newton's
constant and `c` the speed of light, where `Λ > 0` is the cosmological constant of de Sitter space
as in `Physlib.Cosmology.FLRW`. The Gödel metric solves them with `ρ = c² / (8 π G a²)`
(`godelDensity`) and `Λ = -1 / (2 a²)` (`godelCosmologicalConstant`): see
`einstein_sub_cosmological_godel` and `ricci_godel_dust_cosmological`. The cosmological constant
is a fluid with the density `ρ_Λ = Λ c² / (8 π G)` and pressure `p_Λ = -ρ_Λ c²` of
`Cosmology.FLRW.FriedmannEquation.cosmologicalConstantDensity` and
`Cosmology.FLRW.FriedmannEquation.cosmologicalConstantPressure`, so the equations say that `G_{ab}` is
`8 π G / c⁴` times the stress-energy tensor of dust plus this fluid (`einstein_godelMetric_fluid`).

## ii. Key results

- `ricci_godelMetric_expr` : the Ricci tensor in terms of the closed form Christoffel symbols.
- `ricci_godelMetric` : `R_{ab} = u_a u_b / (a² c²)`.
- `ricciScalar_godelMetric` : the Ricci scalar is `1 / a²`.
- `einstein_godelMetric` : the Einstein tensor is `u_a u_b / (a² c²) - g_{ab} / (2 a²)`.
- `einstein_sub_cosmological_godel` : `G_{ab} - Λ g_{ab} = (8 π G / c⁴) ρ u_a u_b`.
- `ricci_godel_dust_cosmological` : the trace-reversed form of the same equation.
- `einstein_godelMetric_fluid` : `G_{ab}` is `8 π G / c⁴` times the stress-energy tensor of dust
  plus the cosmological constant fluid.

## iii. Table of contents

- A. The dust four-velocity
- B. The Ricci tensor
- C. Einstein's equations with dust and a cosmological constant

## iv. References

- K. Gödel, *An example of a new type of cosmological solutions of Einstein's field equations of
  gravitation*, Rev. Mod. Phys. 21, 447 (1949) (in the signature `(+,-,-,-)`, with `c = 1`).
- S. W. Hawking and G. F. R. Ellis, *The Large Scale Structure of Space-Time*, Section 5.2 (in the
  opposite sign convention `(-,+,+,+)` and units with `G = c = 1`).

-/

@[expose] public section

noncomputable section

namespace GeneralRelativity

open Real

/-!

## A. The dust four-velocity

-/

/-- The covariant dust four-velocity `u_a = g_{a t}` of the Gödel universe, the lowering of the
vector `u^a = ∂_t`. -/
def godelVelocityLower (a : ℝ) (c : SpeedOfLight) (y : Fin 4 → ℝ) (i : Fin 4) : ℝ :=
  godelMetric a c y i 0

/-- The dust four-velocity `∂_t` is normalised to `g_{tt} = c²`. -/
lemma godelVelocityLower_apply_zero (a : ℝ) (c : SpeedOfLight) (y : Fin 4 → ℝ) :
    godelVelocityLower a c y 0 = (c : ℝ) ^ 2 := by
  simp [godelVelocityLower, godelMetric, godelMetricR]

/-!

## B. The Ricci tensor

-/

/-- The coordinate derivatives of the Christoffel symbols of the Gödel metric: only `∂_r` is
non-zero. -/
lemma coordDeriv_christoffel_godelMetric {a : ℝ} (ha : 0 < a) (c : SpeedOfLight)
    {x : Fin 4 → ℝ} (hx : x ∈ godelDomain) (i j k e : Fin 4) :
    coordDeriv (fun y => christoffel (godelMetric a c) y i j k) x e
      = if e = 1 then godelGamma' a c i j k (x 1) else 0 := by
  have hr : 0 < x 1 := hx
  have hs : sinh (x 1) ≠ 0 := (sinh_pos_iff.2 hr).ne'
  have hc : cosh (x 1) ≠ 0 := (cosh_pos _).ne'
  have hcongr : (fun y => christoffel (godelMetric a c) y i j k)
      =ᶠ[nhds x] fun y => godelGamma a c i j k (y 1) := by
    filter_upwards [isOpen_godelDomain.mem_nhds hx] with y hy
    exact christoffel_godelMetric ha c hy i j k
  have h := hasDerivAt_godelGamma a c hs hc i j k
  rw [coordDeriv_congr hcongr e, coordDeriv_comp_proj 1 h.differentiableAt, h.deriv]

/-- The Ricci tensor of the Gödel metric in terms of the closed forms of the Christoffel symbols
and their derivatives. -/
lemma ricci_godelMetric_expr {a : ℝ} (ha : 0 < a) (c : SpeedOfLight) {x : Fin 4 → ℝ}
    (hx : x ∈ godelDomain) (b d : Fin 4) :
    ricci (godelMetric a c) x b d = ∑ i, (
      (if i = 1 then godelGamma' a c i d b (x 1) else 0)
      - (if d = 1 then godelGamma' a c i i b (x 1) else 0)
      + ∑ e, (godelGamma a c i i e (x 1) * godelGamma a c e d b (x 1)
        - godelGamma a c i d e (x 1) * godelGamma a c e i b (x 1))) := by
  simp only [ricci, riemann, coordDeriv_christoffel_godelMetric ha c hx,
    christoffel_godelMetric ha c hx]

/-- The Ricci tensor of the Gödel metric is `R_{ab} = u_a u_b / (a² c²)`, where `u_a = g_{a t}`
is the dust four-velocity. -/
lemma ricci_godelMetric {a : ℝ} (ha : 0 < a) (c : SpeedOfLight) {x : Fin 4 → ℝ}
    (hx : x ∈ godelDomain) (b d : Fin 4) :
    ricci (godelMetric a c) x b d
      = godelVelocityLower a c x b * godelVelocityLower a c x d / (a ^ 2 * (c : ℝ) ^ 2) := by
  have hr : 0 < x 1 := hx
  have hs : sinh (x 1) ≠ 0 := (sinh_pos_iff.2 hr).ne'
  have hc : cosh (x 1) ≠ 0 := (cosh_pos _).ne'
  have hc0 : (c : ℝ) ≠ 0 := c.val_pos.ne'
  have ha0 : a ≠ 0 := ha.ne'
  have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hcs := cosh_sq (x 1)
  rw [ricci_godelMetric_expr ha c hx]
  fin_cases b <;> fin_cases d <;>
  simp [Fin.sum_univ_four, godelGamma, godelGamma', godelVelocityLower, godelMetric,
    godelMetricR]
  all_goals field_simp
  all_goals (simp only [h2, hcs]; ring1)

/-- The Ricci scalar of the Gödel metric is `1 / a²`. -/
lemma ricciScalar_godelMetric {a : ℝ} (ha : 0 < a) (c : SpeedOfLight) {x : Fin 4 → ℝ}
    (hx : x ∈ godelDomain) : ricciScalar (godelMetric a c) x = 1 / a ^ 2 := by
  have hr : 0 < x 1 := hx
  have hs : sinh (x 1) ≠ 0 := (sinh_pos_iff.2 hr).ne'
  have hc : cosh (x 1) ≠ 0 := (cosh_pos _).ne'
  have hc0 : (c : ℝ) ≠ 0 := c.val_pos.ne'
  have ha0 : a ≠ 0 := ha.ne'
  have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hcs := cosh_sq (x 1)
  simp only [ricciScalar, ricci_godelMetric ha c hx, godelMetric_inv ha c hx]
  simp [Fin.sum_univ_four, godelMetricInvR, godelVelocityLower, godelMetric, godelMetricR]
  field_simp
  simp only [h2, hcs]
  ring

/-- The Einstein tensor of the Gödel metric is
`G_{ab} = u_a u_b / (a² c²) - g_{ab} / (2 a²)`. -/
lemma einstein_godelMetric {a : ℝ} (ha : 0 < a) (c : SpeedOfLight) {x : Fin 4 → ℝ}
    (hx : x ∈ godelDomain) (i j : Fin 4) :
    einstein (godelMetric a c) x i j
      = godelVelocityLower a c x i * godelVelocityLower a c x j / (a ^ 2 * (c : ℝ) ^ 2)
        - godelMetric a c x i j / (2 * a ^ 2) := by
  simp only [einstein, ricci_godelMetric ha c hx, ricciScalar_godelMetric ha c hx]
  field_simp

/-!

## C. Einstein's equations with dust and a cosmological constant

-/

/-- The mass density `ρ = c² / (8 π G a²)` of the dust of the Gödel universe with length scale
`a`.

- `G : ℝ` is Newton's constant.
- `c : SpeedOfLight` is the speed of light; take `c = 1` for units in which it is one.
- `a : ℝ` is the length scale of the universe. -/
def godelDensity (G : ℝ) (c : SpeedOfLight) (a : ℝ) : ℝ :=
  (c : ℝ) ^ 2 / (8 * π * G * a ^ 2)

/-- The cosmological constant `Λ = -1 / (2 a²)` of the Gödel universe with length scale `a`. It is
negative: the cosmological constant fluid has negative energy density. -/
def godelCosmologicalConstant (a : ℝ) : ℝ := -1 / (2 * a ^ 2)

/-- The Gödel metric solves Einstein's equations with pressureless dust and a cosmological
constant: `G_{ab} - Λ g_{ab} = (8 π G / c⁴) ρ u_a u_b`, in the signature `(+,-,-,-)`. -/
theorem einstein_sub_cosmological_godel {a G : ℝ} (ha : 0 < a) (hG : G ≠ 0) (c : SpeedOfLight)
    {x : Fin 4 → ℝ} (hx : x ∈ godelDomain) (i j : Fin 4) :
    einstein (godelMetric a c) x i j - godelCosmologicalConstant a * godelMetric a c x i j
      = 8 * π * G / (c : ℝ) ^ 4 * godelDensity G c a
        * godelVelocityLower a c x i * godelVelocityLower a c x j := by
  have hc0 : (c : ℝ) ≠ 0 := c.val_pos.ne'
  have ha0 : a ≠ 0 := ha.ne'
  rw [einstein_godelMetric ha c hx]
  simp only [godelCosmologicalConstant, godelDensity]
  field_simp
  ring

/-- The trace-reversed form of Einstein's equations with dust and a cosmological constant:
`R_{ab} = (8 π G / c⁴) ρ u_a u_b - (4 π G ρ / c² + Λ) g_{ab}`. -/
lemma ricci_godel_dust_cosmological {a G : ℝ} (ha : 0 < a) (hG : G ≠ 0) (c : SpeedOfLight)
    {x : Fin 4 → ℝ} (hx : x ∈ godelDomain) (i j : Fin 4) :
    ricci (godelMetric a c) x i j
      = 8 * π * G / (c : ℝ) ^ 4 * godelDensity G c a
          * godelVelocityLower a c x i * godelVelocityLower a c x j
        - (4 * π * G * godelDensity G c a / (c : ℝ) ^ 2 + godelCosmologicalConstant a)
          * godelMetric a c x i j := by
  have hc0 : (c : ℝ) ≠ 0 := c.val_pos.ne'
  have ha0 : a ≠ 0 := ha.ne'
  rw [ricci_godelMetric ha c hx]
  simp only [godelCosmologicalConstant, godelDensity]
  field_simp
  ring

/-- The cosmological constant fluid of the Gödel universe, with the density and pressure of
`Cosmology.FLRW.FriedmannEquation.cosmologicalConstantDensity` and
`Cosmology.FLRW.FriedmannEquation.cosmologicalConstantPressure`, has density `-ρ / 2`, where `ρ` is the
density of the dust. -/
lemma cosmologicalConstantDensity_godel {a G : ℝ} (ha : 0 < a) (hG : G ≠ 0) (c : SpeedOfLight) :
    Cosmology.FLRW.FriedmannEquation.cosmologicalConstantDensity (godelCosmologicalConstant a) G c
      = -(godelDensity G c a / 2) := by
  have ha0 : a ≠ 0 := ha.ne'
  have hπ := Real.pi_ne_zero
  simp only [Cosmology.FLRW.FriedmannEquation.cosmologicalConstantDensity, godelCosmologicalConstant,
    godelDensity]
  field_simp

/-- Einstein's equations of the Gödel universe as an equation of tensors: `G_{ab}` is
`8 π G / c⁴` times the stress-energy tensor of pressureless dust of density `ρ` and four-velocity
`∂_t` plus that of the cosmological constant fluid. -/
theorem einstein_godelMetric_fluid {a G : ℝ} (ha : 0 < a) (hG : G ≠ 0) (c : SpeedOfLight)
    {x : Fin 4 → ℝ} (hx : x ∈ godelDomain) (i j : Fin 4) :
    einstein (godelMetric a c) x i j = 8 * π * G / (c : ℝ) ^ 4 *
      (perfectFluid (Matrix.toBilin' (godelMetric a c x)) (Pi.single 0 1) (godelDensity G c a) 0 c
          (Pi.single i 1) (Pi.single j 1)
        + perfectFluid (Matrix.toBilin' (godelMetric a c x)) (Pi.single 0 1)
          (Cosmology.FLRW.FriedmannEquation.cosmologicalConstantDensity (godelCosmologicalConstant a) G c)
          (Cosmology.FLRW.FriedmannEquation.cosmologicalConstantPressure (godelCosmologicalConstant a) G c) c
          (Pi.single i 1) (Pi.single j 1)) := by
  have hc0 : (c : ℝ) ≠ 0 := c.val_pos.ne'
  have ha0 : a ≠ 0 := ha.ne'
  have hπ := Real.pi_ne_zero
  have h := einstein_sub_cosmological_godel ha hG c hx i j
  have hs : ∀ p q, godelMetric a c x p q = godelMetric a c x q p := fun p q =>
    ((isLorentzianMetricOn_godelMetric ha c).symm x hx).apply q p
  have hΛ : godelCosmologicalConstant a = 8 * π * G / (c : ℝ) ^ 4 *
      (-(Cosmology.FLRW.FriedmannEquation.cosmologicalConstantPressure
        (godelCosmologicalConstant a) G c)) := by
    rw [Cosmology.FLRW.FriedmannEquation.cosmologicalConstantPressure,
      cosmologicalConstantDensity_godel ha hG c]
    simp only [godelCosmologicalConstant, godelDensity]
    field_simp
  have hρ : Cosmology.FLRW.FriedmannEquation.cosmologicalConstantDensity
      (godelCosmologicalConstant a) G c
      + Cosmology.FLRW.FriedmannEquation.cosmologicalConstantPressure
        (godelCosmologicalConstant a) G c / (c : ℝ) ^ 2 = 0 := by
    rw [Cosmology.FLRW.FriedmannEquation.cosmologicalConstantPressure]
    field_simp
    ring
  simp only [perfectFluid_apply, Matrix.toBilin'_single, hρ, godelVelocityLower] at h ⊢
  rw [hs 0 i, hs 0 j]
  linear_combination h + godelMetric a c x i j * hΛ

end GeneralRelativity
