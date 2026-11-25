/-
Copyright (c) 2026 Harsha Vankayalapati. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harsha Vankayalapati
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Physlib.Relativity.SpeedOfLight
public import PhyslibAlpha.Relativity.General.CoordinateMetric

/-!

# The Gödel metric

The metric of Gödel's rotating universe in standard cylindrical coordinates, and the fact that it
is Lorentzian away from the axis.

## i. Overview

In the coordinates `(t, r, φ, z)` (stored as `x 0, x 1, x 2, x 3`), with `t` a time, `r` a
dimensionless radial coordinate, `φ` an angle and `z` a length, the Gödel metric is, in the
signature `(+,-,-,-)`,
`c² dt² - 4a² dr² + 4a² (sinh⁴ r - sinh² r) dφ² - dz² + 4 √2 a c sinh² r dt dφ`.
Here `c : SpeedOfLight` is the speed of light (take `c = 1` for units in which it is one) and
`a > 0` is the length scale of the universe. It is obtained from the dimensionless form
`4a² (dT² - dr² + (sinh⁴ r - sinh² r) dφ² - dz̃² + 2 √2 sinh² r dT dφ)` of Gödel by `T = c t / (2a)`
and `z̃ = z / (2a)`. The `(t, φ)` block has determinant `-4 a² c² sinh² r cosh² r`, so the metric is
non-degenerate and Lorentzian exactly away from the axis `r = 0`, where the cylindrical
coordinates are singular. Since `g_{φφ} > 0` for `sinh r > 1`, the circles of constant `t`, `r`,
`z` are timelike for `r > r_c = arsinh 1 = ln (1 + √2)`.

## ii. Key results

- `godelMetric` : the Gödel metric field, with `godelMetricR` its matrix at radius `r`.
- `godelDomain` : the open region `r > 0` on which it is regular.
- `godelMetric_bilin` : the bilinear form of the metric in components.
- `isLorentzianMetricOn_godelMetric` : the Gödel metric is Lorentzian on `godelDomain`.

## iii. Table of contents

- A. The metric
- B. The metric is Lorentzian

## iv. References

- K. Gödel, *An example of a new type of cosmological solutions of Einstein's field equations of
  gravitation*, Rev. Mod. Phys. 21, 447 (1949) (in the signature `(+,-,-,-)`, with `c = 1` and the
  length scale `a`).

-/

@[expose] public section

noncomputable section

namespace GeneralRelativity

open Real
open scoped ContDiff

/-!

## A. The metric

-/

/-- The matrix of the Gödel metric at radius `r`, in cylindrical coordinates `(t, r, φ, z)` and
the signature `(+,-,-,-)`.

- `a : ℝ` is the length scale of the universe.
- `c : SpeedOfLight` is the speed of light; take `c = 1` for units in which it is one. -/
def godelMetricR (a : ℝ) (c : SpeedOfLight) (r : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![(c : ℝ) ^ 2, 0, 2 * √2 * a * c * sinh r ^ 2, 0;
    0, -(4 * a ^ 2), 0, 0;
    2 * √2 * a * c * sinh r ^ 2, 0, 4 * a ^ 2 * (sinh r ^ 4 - sinh r ^ 2), 0;
    0, 0, 0, -1]

/-- The Gödel metric
`c² dt² - 4a² dr² + 4a² (sinh⁴ r - sinh² r) dφ² - dz² + 4 √2 a c sinh² r dt dφ` in cylindrical
coordinates `(t, r, φ, z)` and the signature `(+,-,-,-)`.

- `a : ℝ` is the length scale of the universe.
- `c : SpeedOfLight` is the speed of light; take `c = 1` for units in which it is one. -/
def godelMetric (a : ℝ) (c : SpeedOfLight) : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ :=
  fun y => godelMetricR a c (y 1)

/-- The region `r > 0` away from the axis, on which the cylindrical coordinates are regular. -/
def godelDomain : Set (Fin 4 → ℝ) := {y | 0 < y 1}

/-- The region away from the axis is open. -/
lemma isOpen_godelDomain : IsOpen godelDomain :=
  isOpen_lt continuous_const (continuous_apply 1)

/-- The real hyperbolic sine is smooth. -/
lemma contDiff_sinh_real {n : WithTop ℕ∞} : ContDiff ℝ n (sinh : ℝ → ℝ) := by
  have h : (sinh : ℝ → ℝ) = fun x => (exp x - exp (-x)) / 2 := funext Real.sinh_eq
  rw [h]
  exact ((Real.contDiff_exp (n := n)).sub
    ((Real.contDiff_exp (n := n)).comp contDiff_neg)).div_const 2

/-- The bilinear form of the Gödel metric in components. -/
lemma godelMetric_bilin (a : ℝ) (c : SpeedOfLight) (y v w : Fin 4 → ℝ) :
    Matrix.toBilin' (godelMetric a c y) v w = (c : ℝ) ^ 2 * (v 0 * w 0) - 4 * a ^ 2 * (v 1 * w 1)
      - v 3 * w 3 + 2 * √2 * a * c * sinh (y 1) ^ 2 * (v 0 * w 2 + v 2 * w 0)
      + 4 * a ^ 2 * (sinh (y 1) ^ 4 - sinh (y 1) ^ 2) * (v 2 * w 2) := by
  simp [Matrix.toBilin'_apply', godelMetric, godelMetricR, dotProduct, Matrix.mulVec,
    Fin.sum_univ_four]
  ring

/-!

## B. The metric is Lorentzian

-/

/-- The Gödel metric is a Lorentzian metric on the region away from the axis. -/
lemma isLorentzianMetricOn_godelMetric {a : ℝ} (ha : 0 < a) (c : SpeedOfLight) :
    IsLorentzianMetricOn (godelMetric a c) godelDomain where
  isOpen := isOpen_godelDomain
  symm y _ := by
    ext p q
    fin_cases p <;> fin_cases q <;> simp [godelMetric, godelMetricR]
  contDiffOn p q := by
    refine ContDiff.contDiffOn ?_
    have hs : ContDiff ℝ ∞ fun y : Fin 4 → ℝ => sinh (y 1) :=
      contDiff_sinh_real.comp (contDiff_pi.1 contDiff_id (1 : Fin 4))
    fin_cases p <;> fin_cases q <;> simp [godelMetric, godelMetricR] <;> fun_prop
  lorentzian y hy := by
    have hc : 0 < (c : ℝ) := c.val_pos
    have hs : 0 < sinh (y 1) := sinh_pos_iff.2 hy
    have h2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
    refine ⟨fun v w => by simp only [godelMetric_bilin]; ring, Pi.single 0 1, ?_, fun v h hv => ?_⟩
    · rw [godelMetric_bilin]
      simp
    · simp only [godelMetric_bilin, Pi.single_apply] at h
      simp at h
      have hv0 : v 0 = -(2 * √2 * a * sinh (y 1) ^ 2 * v 2) / c := by
        rw [eq_div_iff hc.ne']
        refine mul_left_cancel₀ hc.ne' ?_
        linear_combination h
      have key : Matrix.toBilin' (godelMetric a c y) v v
          = -(4 * a ^ 2 * sinh (y 1) ^ 2 * cosh (y 1) ^ 2 * v 2 ^ 2 + 4 * a ^ 2 * v 1 ^ 2
            + v 3 ^ 2) := by
        rw [godelMetric_bilin, hv0, show cosh (y 1) ^ 2 = sinh (y 1) ^ 2 + 1 from cosh_sq _]
        field_simp
        have h2' : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
        ring_nf
        rw [h2']
        ring
      have hne : v 1 ≠ 0 ∨ v 2 ≠ 0 ∨ v 3 ≠ 0 := by
        by_contra hcon
        simp only [not_or, not_not] at hcon
        refine hv (funext fun i => ?_)
        fin_cases i <;> simp [hcon, hv0]
      rw [key]
      have hch : 0 < cosh (y 1) := cosh_pos _
      have hp : 0 < 4 * a ^ 2 * sinh (y 1) ^ 2 * cosh (y 1) ^ 2 := by positivity
      have ha2 : 0 < 4 * a ^ 2 := by positivity
      rcases hne with h' | h' | h'
      · have := sq_pos_of_ne_zero h'
        nlinarith [sq_nonneg (v 2), sq_nonneg (v 3), mul_nonneg hp.le (sq_nonneg (v 2)),
          mul_pos ha2 this]
      · have := sq_pos_of_ne_zero h'
        nlinarith [sq_nonneg (v 1), sq_nonneg (v 3), mul_pos hp this, mul_nonneg ha2.le (sq_nonneg (v 1))]
      · have := sq_pos_of_ne_zero h'
        nlinarith [sq_nonneg (v 1), sq_nonneg (v 2), mul_nonneg hp.le (sq_nonneg (v 2)),
          mul_nonneg ha2.le (sq_nonneg (v 1))]

end GeneralRelativity
