/-
Copyright (c) 2026 Harsha Vankayalapati. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harsha Vankayalapati
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Physlib.Relativity.SpeedOfLight
public import PhyslibAlpha.Relativity.General.Curvature
public import PhyslibAlpha.Relativity.General.Godel.Metric

/-!

# Christoffel symbols of the Gödel metric

The inverse of the Gödel metric and the closed forms of its Christoffel symbols and their
derivatives.

## i. Overview

The Gödel metric depends only on the radius `r`, so its inverse, its coordinate derivatives and
its Christoffel symbols are explicit functions of `sinh r` and `cosh r`. Only `Γ^r_{tφ}`,
`Γ^r_{φφ}`, `Γ^t_{tr}`, `Γ^t_{rφ}`, `Γ^φ_{tr}`, `Γ^φ_{rφ}` and the ones related by symmetry are
non-zero (`godelGamma`). We prove that `godelGamma` is the Christoffel symbol of `godelMetric`
away from the axis (`christoffel_godelMetric`) and give its `r`-derivative (`godelGamma'`,
`hasDerivAt_godelGamma`), which is the input needed to compute the Ricci tensor.

## ii. Key results

- `godelMetricInvR`, `godelMetric_inv` : the inverse metric.
- `coordDeriv_godelMetric` : only the `r`-derivatives of the metric are non-zero.
- `godelGamma`, `christoffel_godelMetric` : the Christoffel symbols in closed form.
- `godelGamma'`, `hasDerivAt_godelGamma` : their derivatives with respect to `r`.

## iii. Table of contents

- A. The inverse metric
- B. Derivatives of the metric
- C. The Christoffel symbols
- D. Derivatives of the Christoffel symbols

## iv. References

- K. Gödel, *An example of a new type of cosmological solutions of Einstein's field equations of
  gravitation*, Rev. Mod. Phys. 21, 447 (1949).

-/

@[expose] public section

noncomputable section

namespace GeneralRelativity

open Real

/-!

## A. The inverse metric

-/

/-- The inverse of the Gödel metric at radius `r`. -/
def godelMetricInvR (a : ℝ) (c : SpeedOfLight) (r : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![(1 - sinh r ^ 2) / ((c : ℝ) ^ 2 * cosh r ^ 2), 0, √2 / (2 * a * c * cosh r ^ 2), 0;
    0, -(1 / (4 * a ^ 2)), 0, 0;
    √2 / (2 * a * c * cosh r ^ 2), 0, -(1 / (4 * a ^ 2 * (sinh r ^ 2 * cosh r ^ 2))), 0;
    0, 0, 0, -1]

/-- The inverse of the Gödel metric away from the axis. -/
lemma godelMetricR_inv {a : ℝ} (ha : 0 < a) (c : SpeedOfLight) {r : ℝ} (hr : 0 < r) :
    (godelMetricR a c r)⁻¹ = godelMetricInvR a c r := by
  have hs : sinh r ≠ 0 := (sinh_pos_iff.2 hr).ne'
  have hc : cosh r ≠ 0 := (cosh_pos r).ne'
  have hc0 : (c : ℝ) ≠ 0 := c.val_pos.ne'
  have ha0 : a ≠ 0 := ha.ne'
  have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hcs := cosh_sq r
  refine Matrix.inv_eq_right_inv ?_
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [godelMetricR, godelMetricInvR, Matrix.mul_apply, Fin.sum_univ_four] <;>
    field_simp
  all_goals first | ring1 | (rw [h2]; linarith)

/-!

## B. Derivatives of the metric

-/

/-- The `r`-derivative of `godelMetricR`. -/
def godelMetricR' (a : ℝ) (c : SpeedOfLight) (r : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 0, 2 * √2 * a * c * (2 * sinh r * cosh r), 0;
    0, 0, 0, 0;
    2 * √2 * a * c * (2 * sinh r * cosh r), 0,
      4 * a ^ 2 * (4 * sinh r ^ 3 * cosh r - 2 * sinh r * cosh r), 0;
    0, 0, 0, 0]

/-- The derivative of `sinh² r` is `2 sinh r cosh r`. -/
lemma hasDerivAt_sinh_sq (r : ℝ) :
    HasDerivAt (fun r : ℝ => sinh r ^ 2) (2 * sinh r * cosh r) r := by
  have h : HasDerivAt sinh (cosh r) r := Real.hasDerivAt_sinh r
  simpa [mul_assoc] using h.fun_pow 2

/-- The derivative of `sinh⁴ r` is `4 sinh³ r cosh r`. -/
lemma hasDerivAt_sinh_pow_four (r : ℝ) :
    HasDerivAt (fun r : ℝ => sinh r ^ 4) (4 * sinh r ^ 3 * cosh r) r := by
  have h : HasDerivAt sinh (cosh r) r := Real.hasDerivAt_sinh r
  simpa [mul_assoc] using h.fun_pow 4

/-- `godelMetricR'` is the `r`-derivative of `godelMetricR`, entry by entry. -/
lemma hasDerivAt_godelMetricR (a : ℝ) (c : SpeedOfLight) (r : ℝ) (p q : Fin 4) :
    HasDerivAt (fun r => godelMetricR a c r p q) (godelMetricR' a c r p q) r := by
  fin_cases p <;> fin_cases q <;> simp [godelMetricR, godelMetricR'] <;>
    first
    | exact hasDerivAt_const _ _
    | exact (hasDerivAt_sinh_sq r).const_mul _
    | exact (((hasDerivAt_sinh_pow_four r).sub (hasDerivAt_sinh_sq r)).const_mul _).congr_deriv
        (by ring)

/-- The inverse of the Gödel metric field away from the axis. -/
lemma godelMetric_inv {a : ℝ} (ha : 0 < a) (c : SpeedOfLight) {y : Fin 4 → ℝ}
    (hy : y ∈ godelDomain) : (godelMetric a c y)⁻¹ = godelMetricInvR a c (y 1) :=
  godelMetricR_inv ha c hy

/-- The coordinate derivatives of the Gödel metric: only `∂_r` is non-zero. -/
lemma coordDeriv_godelMetric (a : ℝ) (c : SpeedOfLight) (x : Fin 4 → ℝ) (p q b : Fin 4) :
    coordDeriv (fun y => godelMetric a c y p q) x b
      = if b = 1 then godelMetricR' a c (x 1) p q else 0 := by
  have h := hasDerivAt_godelMetricR a c (x 1) p q
  have := coordDeriv_comp_proj (x := x) (A := fun r => godelMetricR a c r p q) 1
    h.differentiableAt b
  rw [h.deriv] at this
  exact this

/-!

## C. The Christoffel symbols

-/

/-- The Christoffel symbol `Γ^a_{bc}` of the Gödel metric as a function of `r`. -/
def godelGamma (a : ℝ) (c : SpeedOfLight) (i j k : Fin 4) (r : ℝ) : ℝ :=
  if i = 1 ∧ ((j = 0 ∧ k = 2) ∨ (j = 2 ∧ k = 0)) then √2 * c / (2 * a) * (sinh r * cosh r)
  else if i = 1 ∧ j = 2 ∧ k = 2 then -(sinh r * cosh r * (1 - 2 * sinh r ^ 2))
  else if i = 0 ∧ ((j = 0 ∧ k = 1) ∨ (j = 1 ∧ k = 0)) then 2 * sinh r / cosh r
  else if i = 0 ∧ ((j = 1 ∧ k = 2) ∨ (j = 2 ∧ k = 1)) then
    2 * √2 * a / c * (sinh r ^ 3 / cosh r)
  else if i = 2 ∧ ((j = 0 ∧ k = 1) ∨ (j = 1 ∧ k = 0)) then
    -(√2 * c / (2 * a) / (sinh r * cosh r))
  else if i = 2 ∧ ((j = 1 ∧ k = 2) ∨ (j = 2 ∧ k = 1)) then 1 / (sinh r * cosh r)
  else 0

/-- The Christoffel symbols of the Gödel metric. -/
lemma christoffel_godelMetric {a : ℝ} (ha : 0 < a) (c : SpeedOfLight) {x : Fin 4 → ℝ}
    (hx : x ∈ godelDomain) (i j k : Fin 4) :
    christoffel (godelMetric a c) x i j k = godelGamma a c i j k (x 1) := by
  have hr : 0 < x 1 := hx
  have hs : sinh (x 1) ≠ 0 := (sinh_pos_iff.2 hr).ne'
  have hc : cosh (x 1) ≠ 0 := (cosh_pos _).ne'
  have hc0 : (c : ℝ) ≠ 0 := c.val_pos.ne'
  have ha0 : a ≠ 0 := ha.ne'
  have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hcs := cosh_sq (x 1)
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
  simp [christoffel, christoffelFirstKind, godelMetric_inv ha c hx,
    coordDeriv_godelMetric, godelMetricR', godelMetricInvR, godelGamma, Fin.sum_univ_four]
  all_goals field_simp
  all_goals first | exact h2 | ring1 | (rw [h2]; ring1)

/-- The `r`-derivative of `godelGamma`. -/
def godelGamma' (a : ℝ) (c : SpeedOfLight) (i j k : Fin 4) (r : ℝ) : ℝ :=
  if i = 1 ∧ ((j = 0 ∧ k = 2) ∨ (j = 2 ∧ k = 0)) then
    √2 * c / (2 * a) * (cosh r ^ 2 + sinh r ^ 2)
  else if i = 1 ∧ j = 2 ∧ k = 2 then
    -((cosh r ^ 2 + sinh r ^ 2) * (1 - 2 * sinh r ^ 2) - 4 * sinh r ^ 2 * cosh r ^ 2)
  else if i = 0 ∧ ((j = 0 ∧ k = 1) ∨ (j = 1 ∧ k = 0)) then
    (2 * cosh r * cosh r - 2 * sinh r * sinh r) / cosh r ^ 2
  else if i = 0 ∧ ((j = 1 ∧ k = 2) ∨ (j = 2 ∧ k = 1)) then
    2 * √2 * a / c * ((3 * sinh r ^ 2 * cosh r * cosh r - sinh r ^ 3 * sinh r) / cosh r ^ 2)
  else if i = 2 ∧ ((j = 0 ∧ k = 1) ∨ (j = 1 ∧ k = 0)) then
    √2 * c / (2 * a) * ((cosh r ^ 2 + sinh r ^ 2) / (sinh r * cosh r) ^ 2)
  else if i = 2 ∧ ((j = 1 ∧ k = 2) ∨ (j = 2 ∧ k = 1)) then
    -((cosh r ^ 2 + sinh r ^ 2) / (sinh r * cosh r) ^ 2)
  else 0

/-!

## D. Derivatives of the Christoffel symbols

-/

section Derivatives

variable {r : ℝ}

/-- The derivative of `sinh r cosh r` is `cosh² r + sinh² r`. -/
lemma hasDerivAt_sinh_mul_cosh (r : ℝ) :
    HasDerivAt (fun r : ℝ => sinh r * cosh r) (cosh r ^ 2 + sinh r ^ 2) r := by
  have h1 : HasDerivAt sinh (cosh r) r := Real.hasDerivAt_sinh r
  have h2 : HasDerivAt cosh (sinh r) r := Real.hasDerivAt_cosh r
  convert h1.mul h2 using 1
  ring

/-- `godelGamma'` is the `r`-derivative of `godelGamma`, away from the axis. -/
lemma hasDerivAt_godelGamma (a : ℝ) (c : SpeedOfLight) (hs : sinh r ≠ 0) (hc : cosh r ≠ 0)
    (i j k : Fin 4) : HasDerivAt (godelGamma a c i j k) (godelGamma' a c i j k r) r := by
  have h1 : HasDerivAt sinh (cosh r) r := Real.hasDerivAt_sinh r
  have h2 : HasDerivAt cosh (sinh r) r := Real.hasDerivAt_cosh r
  have hsc := hasDerivAt_sinh_mul_cosh r
  have hne : sinh r * cosh r ≠ 0 := mul_ne_zero hs hc
  unfold godelGamma godelGamma'
  split_ifs
  · exact hsc.const_mul _
  · have := (hsc.mul (((hasDerivAt_sinh_sq r).const_mul 2).const_sub 1)).neg
    refine HasDerivAt.congr_deriv this ?_
    ring
  · have := (h1.const_mul 2).div h2 hc
    refine HasDerivAt.congr_deriv this ?_
    ring
  · have := ((((hasDerivAt_pow 3 (sinh r)).comp r h1).div h2 hc).const_mul (2 * √2 * a / c))
    refine HasDerivAt.congr_deriv this ?_
    simp
  · have := ((hsc.inv hne).const_mul (√2 * c / (2 * a))).neg
    refine HasDerivAt.congr_deriv (this.congr_of_eventuallyEq ?_) ?_
    · exact Filter.Eventually.of_forall fun r => by simp [div_eq_mul_inv]
    · simp [div_eq_mul_inv]
      ring
  · have := (hasDerivAt_const r (1 : ℝ)).div hsc hne
    refine HasDerivAt.congr_deriv this ?_
    ring
  · exact hasDerivAt_const _ _

end Derivatives

end GeneralRelativity
