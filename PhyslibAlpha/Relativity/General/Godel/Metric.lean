/-
Copyright (c) 2026 Harsha Vankayalapati. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harsha Vankayalapati
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import PhyslibAlpha.Relativity.General.CoordinateMetric

/-!

# The Gödel metric

The metric of Gödel's rotating universe in standard cylindrical coordinates, and the fact that it
is Lorentzian away from the axis.

## i. Overview

In the coordinates `(t, r, φ, z)` (stored as `x 0, x 1, x 2, x 3`) the Gödel metric, with the
length scale normalised so that `4 a² = 1`, is
`-dt² + dr² - (sinh⁴ r - sinh² r) dφ² + dz² - 2 √2 sinh² r dt dφ`.
The `(t, φ)` block has determinant `-sinh² r cosh² r`, so the metric is non-degenerate and of
signature `(-,+,+,+)` exactly away from the axis `r = 0`, where the cylindrical coordinates are
singular. Since `g_{φφ} < 0` for `sinh r < 1`, the circles of constant `t`, `r`, `z` are timelike
for `r > r_c = arsinh 1 = ln (1 + √2)`.

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
  gravitation*, Rev. Mod. Phys. 21, 447 (1949).

-/

@[expose] public section

noncomputable section

namespace GeneralRelativity

open Real
open scoped ContDiff

/-!

## A. The metric

-/

/-- The matrix of the Gödel metric at radius `r`, in cylindrical coordinates `(t, r, φ, z)`. -/
def godelMetricR (r : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![-1, 0, -(√2 * sinh r ^ 2), 0;
    0, 1, 0, 0;
    -(√2 * sinh r ^ 2), 0, sinh r ^ 2 - sinh r ^ 4, 0;
    0, 0, 0, 1]

/-- The Gödel metric `-dt² + dr² - (sinh⁴ r - sinh² r) dφ² + dz² - 2 √2 sinh² r dt dφ` in
cylindrical coordinates `(t, r, φ, z)`, with length scale `a = 1/2`. -/
def godelMetric : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ :=
  fun y => godelMetricR (y 1)

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
lemma godelMetric_bilin (y v w : Fin 4 → ℝ) :
    Matrix.toBilin' (godelMetric y) v w = -(v 0 * w 0) + v 1 * w 1 + v 3 * w 3
      - √2 * sinh (y 1) ^ 2 * (v 0 * w 2 + v 2 * w 0)
      + (sinh (y 1) ^ 2 - sinh (y 1) ^ 4) * (v 2 * w 2) := by
  simp [Matrix.toBilin'_apply', godelMetric, godelMetricR, dotProduct, Matrix.mulVec,
    Fin.sum_univ_four]
  ring

/-!

## B. The metric is Lorentzian

-/

/-- The Gödel metric is a Lorentzian metric on the region away from the axis. -/
lemma isLorentzianMetricOn_godelMetric : IsLorentzianMetricOn godelMetric godelDomain where
  isOpen := isOpen_godelDomain
  symm y _ := by
    ext p q
    fin_cases p <;> fin_cases q <;> simp [godelMetric, godelMetricR]
  contDiffOn a b := by
    refine ContDiff.contDiffOn ?_
    have hs : ContDiff ℝ ∞ fun y : Fin 4 → ℝ => sinh (y 1) :=
      contDiff_sinh_real.comp (contDiff_pi.1 contDiff_id (1 : Fin 4))
    fin_cases a <;> fin_cases b <;> simp [godelMetric, godelMetricR] <;> fun_prop
  lorentzian y hy := by
    refine ⟨fun v w => by simp only [godelMetric_bilin]; ring, Pi.single 0 1, ?_, fun v h hv => ?_⟩
    · rw [godelMetric_bilin]
      simp
    · simp only [godelMetric_bilin, Pi.single_apply] at h
      simp at h
      have hv0 : v 0 = -(√2 * sinh (y 1) ^ 2 * v 2) := by linarith
      have hne : v 1 ≠ 0 ∨ v 2 ≠ 0 ∨ v 3 ≠ 0 := by
        by_contra hcon
        simp only [not_or, not_not] at hcon
        refine hv (funext fun i => ?_)
        fin_cases i <;> simp [hcon, hv0]
      have hs : 0 < sinh (y 1) := sinh_pos_iff.2 hy
      have hc : cosh (y 1) ^ 2 = sinh (y 1) ^ 2 + 1 := cosh_sq (y 1)
      have key : Matrix.toBilin' (godelMetric y) v v
          = sinh (y 1) ^ 2 * cosh (y 1) ^ 2 * v 2 ^ 2 + v 1 ^ 2 + v 3 ^ 2 := by
        rw [godelMetric_bilin, hv0, hc]
        have : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
        ring_nf
        have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
        rw [h2]
        ring
      rw [key]
      have hp : 0 < sinh (y 1) ^ 2 * cosh (y 1) ^ 2 := by positivity
      rcases hne with h' | h' | h'
      · have := sq_pos_of_ne_zero h'
        nlinarith [sq_nonneg (v 2), sq_nonneg (v 3), mul_nonneg hp.le (sq_nonneg (v 2))]
      · have := sq_pos_of_ne_zero h'
        nlinarith [sq_nonneg (v 1), sq_nonneg (v 3), mul_pos hp this]
      · have := sq_pos_of_ne_zero h'
        nlinarith [sq_nonneg (v 1), sq_nonneg (v 2), mul_nonneg hp.le (sq_nonneg (v 2))]

end GeneralRelativity
