/-
Copyright (c) 2026 Harsha Vankayalapati. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harsha Vankayalapati
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import PhyslibAlpha.Relativity.General.Curvature
public import PhyslibAlpha.Relativity.General.Godel.Metric

@[expose] public section

noncomputable section

namespace GeneralRelativity

open Real

/-- The inverse of the Gödel metric at radius `r`. -/
def godelMetricInvR (r : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![(sinh r ^ 2 - 1) / cosh r ^ 2, 0, -(√2 / cosh r ^ 2), 0;
    0, 1, 0, 0;
    -(√2 / cosh r ^ 2), 0, 1 / (sinh r ^ 2 * cosh r ^ 2), 0;
    0, 0, 0, 1]

lemma godelMetricR_inv {r : ℝ} (hr : 0 < r) : (godelMetricR r)⁻¹ = godelMetricInvR r := by
  have hs : sinh r ≠ 0 := (sinh_pos_iff.2 hr).ne'
  have hc : cosh r ≠ 0 := (cosh_pos r).ne'
  have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hcs := cosh_sq r
  refine Matrix.inv_eq_right_inv ?_
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [godelMetricR, godelMetricInvR, Matrix.mul_apply, Fin.sum_univ_four] <;>
    field_simp
  all_goals first | ring1 | (rw [h2]; linarith)

/-- The `r`-derivative of `godelMetricR`. -/
def godelMetricR' (r : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 0, -(√2 * (2 * sinh r * cosh r)), 0;
    0, 0, 0, 0;
    -(√2 * (2 * sinh r * cosh r)), 0, 2 * sinh r * cosh r - 4 * sinh r ^ 3 * cosh r, 0;
    0, 0, 0, 0]

lemma hasDerivAt_sinh_sq (r : ℝ) : HasDerivAt (fun r : ℝ => sinh r ^ 2) (2 * sinh r * cosh r) r := by
  have h : HasDerivAt sinh (cosh r) r := Real.hasDerivAt_sinh r
  simpa [mul_assoc] using h.fun_pow 2

lemma hasDerivAt_sinh_pow_four (r : ℝ) :
    HasDerivAt (fun r : ℝ => sinh r ^ 4) (4 * sinh r ^ 3 * cosh r) r := by
  have h : HasDerivAt sinh (cosh r) r := Real.hasDerivAt_sinh r
  simpa [mul_assoc] using h.fun_pow 4

lemma hasDerivAt_godelMetricR (r : ℝ) (p q : Fin 4) :
    HasDerivAt (fun r => godelMetricR r p q) (godelMetricR' r p q) r := by
  fin_cases p <;> fin_cases q <;> simp [godelMetricR, godelMetricR'] <;>
    first
    | exact hasDerivAt_const _ _
    | exact ((hasDerivAt_sinh_sq r).const_mul _).neg
    | exact (hasDerivAt_sinh_sq r).sub (hasDerivAt_sinh_pow_four r)

lemma godelMetric_inv {y : Fin 4 → ℝ} (hy : y ∈ godelDomain) :
    (godelMetric y)⁻¹ = godelMetricInvR (y 1) :=
  godelMetricR_inv hy

/-- The coordinate derivatives of the Gödel metric: only `∂_r` is non-zero. -/
lemma coordDeriv_godelMetric (x : Fin 4 → ℝ) (p q b : Fin 4) :
    coordDeriv (fun y => godelMetric y p q) x b
      = if b = 1 then godelMetricR' (x 1) p q else 0 := by
  have h := hasDerivAt_godelMetricR (x 1) p q
  have := coordDeriv_comp_proj (x := x) (A := fun r => godelMetricR r p q) 1
    h.differentiableAt b
  rw [h.deriv] at this
  exact this

/-- The Christoffel symbol `Γ^a_{bc}` of the Gödel metric as a function of `r`. -/
def godelGamma (a b c : Fin 4) (r : ℝ) : ℝ :=
  if a = 1 ∧ ((b = 0 ∧ c = 2) ∨ (b = 2 ∧ c = 0)) then √2 * (sinh r * cosh r)
  else if a = 1 ∧ b = 2 ∧ c = 2 then -(sinh r * cosh r * (1 - 2 * sinh r ^ 2))
  else if a = 0 ∧ ((b = 0 ∧ c = 1) ∨ (b = 1 ∧ c = 0)) then 2 * sinh r / cosh r
  else if a = 0 ∧ ((b = 1 ∧ c = 2) ∨ (b = 2 ∧ c = 1)) then √2 * sinh r ^ 3 / cosh r
  else if a = 2 ∧ ((b = 0 ∧ c = 1) ∨ (b = 1 ∧ c = 0)) then -(√2 / (sinh r * cosh r))
  else if a = 2 ∧ ((b = 1 ∧ c = 2) ∨ (b = 2 ∧ c = 1)) then 1 / (sinh r * cosh r)
  else 0

/-- The Christoffel symbols of the Gödel metric. -/
lemma christoffel_godelMetric {x : Fin 4 → ℝ} (hx : x ∈ godelDomain) (a b c : Fin 4) :
    christoffel godelMetric x a b c = godelGamma a b c (x 1) := by
  have hr : 0 < x 1 := hx
  have hs : sinh (x 1) ≠ 0 := (sinh_pos_iff.2 hr).ne'
  have hc : cosh (x 1) ≠ 0 := (cosh_pos _).ne'
  have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hcs := cosh_sq (x 1)
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
  simp [christoffel, christoffelFirstKind, godelMetric_inv hx,
    coordDeriv_godelMetric, godelMetricR', godelMetricInvR, godelGamma, Fin.sum_univ_four]
  all_goals field_simp
  all_goals first | exact h2 | ring1 | (rw [h2]; ring1)

/-- The `r`-derivative of `godelGamma`. -/
def godelGamma' (a b c : Fin 4) (r : ℝ) : ℝ :=
  if a = 1 ∧ ((b = 0 ∧ c = 2) ∨ (b = 2 ∧ c = 0)) then √2 * (cosh r ^ 2 + sinh r ^ 2)
  else if a = 1 ∧ b = 2 ∧ c = 2 then
    -((cosh r ^ 2 + sinh r ^ 2) * (1 - 2 * sinh r ^ 2) - 4 * sinh r ^ 2 * cosh r ^ 2)
  else if a = 0 ∧ ((b = 0 ∧ c = 1) ∨ (b = 1 ∧ c = 0)) then
    (2 * cosh r * cosh r - 2 * sinh r * sinh r) / cosh r ^ 2
  else if a = 0 ∧ ((b = 1 ∧ c = 2) ∨ (b = 2 ∧ c = 1)) then
    (√2 * (3 * sinh r ^ 2 * cosh r) * cosh r - √2 * sinh r ^ 3 * sinh r) / cosh r ^ 2
  else if a = 2 ∧ ((b = 0 ∧ c = 1) ∨ (b = 1 ∧ c = 0)) then
    √2 * (cosh r ^ 2 + sinh r ^ 2) / (sinh r * cosh r) ^ 2
  else if a = 2 ∧ ((b = 1 ∧ c = 2) ∨ (b = 2 ∧ c = 1)) then
    -((cosh r ^ 2 + sinh r ^ 2) / (sinh r * cosh r) ^ 2)
  else 0

section Derivatives

variable {r : ℝ}

lemma hasDerivAt_sinh_mul_cosh (r : ℝ) :
    HasDerivAt (fun r : ℝ => sinh r * cosh r) (cosh r ^ 2 + sinh r ^ 2) r := by
  have h1 : HasDerivAt sinh (cosh r) r := Real.hasDerivAt_sinh r
  have h2 : HasDerivAt cosh (sinh r) r := Real.hasDerivAt_cosh r
  convert h1.mul h2 using 1
  ring

lemma hasDerivAt_godelGamma (hs : sinh r ≠ 0) (hc : cosh r ≠ 0) (a b c : Fin 4) :
    HasDerivAt (godelGamma a b c) (godelGamma' a b c r) r := by
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
  · have := (((hasDerivAt_pow 3 (sinh r)).comp r h1).const_mul (√2)).div h2 hc
    refine HasDerivAt.congr_deriv this ?_
    simp
  · have := ((hsc.inv hne).const_mul (√2)).neg
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
