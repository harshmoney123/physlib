/-
Copyright (c) 2026 Harsha Vankayalapati. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harsha Vankayalapati
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import PhyslibAlpha.Relativity.General.Curvature

/-!

# The Schwarzschild metric and its Christoffel symbols

The Schwarzschild metric in Schwarzschild coordinates on the exterior region `r > 2M`.

## i. Overview

In coordinates `(t, r, θ, φ)` and units `G = c = 1` (so `M` is the mass in units of length) the
Schwarzschild metric is
`-(1 - 2M/r) dt² + (1 - 2M/r)⁻¹ dr² + r² dθ² + r² sin²θ dφ²`.
It is a Lorentzian metric field on the region `2M < r`, `0 < θ < π`
(`isLorentzianMetricOn_schwarzschildMetric`). We compute all its Christoffel symbols
(`christoffel_schwarzschild`). Each one is a product of a function of `r` and a function of `θ`
(`schwarzschildGammaR`, `schwarzschildGammaTheta`), whose derivatives are recorded in
`hasDerivAt_gammaR` and `hasDerivAt_gammaTheta`.

## ii. Key results

- `schwarzschildMetric` : the metric field.
- `schwarzschildDomain` : the exterior region on which it is Lorentzian.
- `isLorentzianMetricOn_schwarzschildMetric` : it is a Lorentzian metric on that region.
- `schwarzschildMetric_inv` : the inverse metric.
- `christoffel_schwarzschild` : the Christoffel symbols.

## iii. Table of contents

- A. The metric
- B. Closed form of the Christoffel symbols
- C. Derivatives of the Christoffel symbols
- D. Derivatives of the metric
- E. The Christoffel symbols

## iv. References

- K. Schwarzschild, *Über das Gravitationsfeld eines Massenpunktes nach der Einsteinschen
  Theorie*, Sitzungsber. Preuss. Akad. Wiss. (1916).
- R. M. Wald, *General Relativity*, Chapter 6.

-/

@[expose] public section

noncomputable section

namespace GeneralRelativity

open Real

/-!

## A. The metric

-/

/-- The Schwarzschild metric `-(1-2M/r) dt² + (1-2M/r)⁻¹ dr² + r² dθ² + r² sin²θ dφ²` in
Schwarzschild coordinates `(t, r, θ, φ)`, in units `G = c = 1`, where `M` is the mass. -/
def schwarzschildMetric (M : ℝ) : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ :=
  fun y => Matrix.diagonal ![-(1 - 2 * M / y 1), (1 - 2 * M / y 1)⁻¹, y 1 ^ 2,
    y 1 ^ 2 * sin (y 2) ^ 2]

/-- The exterior region `r > 2M` with `0 < θ < π`, on which the coordinates are regular. -/
def schwarzschildDomain (M : ℝ) : Set (Fin 4 → ℝ) :=
  {y | 2 * M < y 1 ∧ 0 < y 2 ∧ y 2 < π}

lemma isOpen_schwarzschildDomain (M : ℝ) : IsOpen (schwarzschildDomain M) :=
  (isOpen_lt continuous_const (continuous_apply 1)).inter
    ((isOpen_lt continuous_const (continuous_apply 2)).inter
      (isOpen_lt (continuous_apply 2) continuous_const))

section Domain

variable {M : ℝ} {x : Fin 4 → ℝ}

lemma schwarzschildDomain.pos (hM : 0 < M) (hx : x ∈ schwarzschildDomain M) : 0 < x 1 := by
  have := hx.1; linarith

lemma schwarzschildDomain.sub_pos (hx : x ∈ schwarzschildDomain M) : 0 < x 1 - 2 * M := by
  have := hx.1; linarith

lemma schwarzschildDomain.sin_pos (hx : x ∈ schwarzschildDomain M) : 0 < sin (x 2) :=
  Real.sin_pos_of_pos_of_lt_pi hx.2.1 hx.2.2

lemma schwarzschildDomain.one_sub_pos (hM : 0 < M) (hx : x ∈ schwarzschildDomain M) :
    0 < 1 - 2 * M / x 1 := by
  have h1 := schwarzschildDomain.pos hM hx
  have h2 := schwarzschildDomain.sub_pos hx
  have : 1 - 2 * M / x 1 = (x 1 - 2 * M) / x 1 := by field_simp
  rw [this]; positivity

/-- The Schwarzschild metric is a Lorentzian metric on the exterior region. -/
lemma isLorentzianMetricOn_schwarzschildMetric (hM : 0 < M) :
    IsLorentzianMetricOn (schwarzschildMetric M) (schwarzschildDomain M) where
  isOpen := isOpen_schwarzschildDomain M
  symm _ _ := Matrix.isSymm_diagonal _
  contDiffOn a b := by
    unfold schwarzschildMetric
    intro y hy
    have h1 := schwarzschildDomain.pos hM hy
    have h2 := schwarzschildDomain.one_sub_pos hM hy
    by_cases hab : a = b
    · subst hab
      refine ContDiffAt.contDiffWithinAt ?_
      fin_cases a <;> simp [Matrix.diagonal_apply_eq]
      · fun_prop (disch := positivity)
      · exact ContDiffAt.inv (by fun_prop (disch := positivity)) h2.ne'
      · fun_prop
      · fun_prop
    · simp [Matrix.diagonal_apply_ne _ hab]
      exact contDiffWithinAt_const
  lorentzian y hy := by
    have h1 := schwarzschildDomain.pos hM hy
    have h2 := schwarzschildDomain.one_sub_pos hM hy
    have h3 := schwarzschildDomain.sin_pos hy
    refine isLorentzian_diagonal_four ?_ ?_ ?_ ?_ <;> simp
    · linarith
    · linarith
    · positivity
    · positivity

end Domain


/-!

## B. Closed form of the Christoffel symbols

-/

/-- The `r`-dependent factor of the Christoffel symbol `Γ^a_{bc}` of the Schwarzschild metric. -/
def schwarzschildGammaR (M : ℝ) (a b c : Fin 4) : ℝ → ℝ :=
  if a = 0 ∧ ((b = 0 ∧ c = 1) ∨ (b = 1 ∧ c = 0)) then fun r => M / (r * (r - 2 * M))
  else if a = 1 ∧ b = 0 ∧ c = 0 then fun r => M * (r - 2 * M) / r ^ 3
  else if a = 1 ∧ b = 1 ∧ c = 1 then fun r => -(M / (r * (r - 2 * M)))
  else if a = 1 ∧ ((b = 2 ∧ c = 2) ∨ (b = 3 ∧ c = 3)) then fun r => -(r - 2 * M)
  else if (a = 2 ∨ a = 3) ∧ ((b = 1 ∧ c = a) ∨ (b = a ∧ c = 1)) then fun r => r⁻¹
  else if (a = 2 ∧ b = 3 ∧ c = 3) ∨ (a = 3 ∧ ((b = 2 ∧ c = 3) ∨ (b = 3 ∧ c = 2))) then
    fun _ => 1
  else fun _ => 0

/-- The `r`-derivative of `schwarzschildGammaR`. -/
def schwarzschildGammaR' (M : ℝ) (a b c : Fin 4) : ℝ → ℝ :=
  if a = 0 ∧ ((b = 0 ∧ c = 1) ∨ (b = 1 ∧ c = 0)) then
    fun r => -(M * (2 * r - 2 * M)) / (r ^ 2 * (r - 2 * M) ^ 2)
  else if a = 1 ∧ b = 0 ∧ c = 0 then fun r => M * (6 * M - 2 * r) / r ^ 4
  else if a = 1 ∧ b = 1 ∧ c = 1 then fun r => M * (2 * r - 2 * M) / (r ^ 2 * (r - 2 * M) ^ 2)
  else if a = 1 ∧ ((b = 2 ∧ c = 2) ∨ (b = 3 ∧ c = 3)) then fun _ => -1
  else if (a = 2 ∨ a = 3) ∧ ((b = 1 ∧ c = a) ∨ (b = a ∧ c = 1)) then fun r => -(r ^ 2)⁻¹
  else fun _ => 0

/-- The `θ`-dependent factor of the Christoffel symbol `Γ^a_{bc}` of the Schwarzschild metric. -/
def schwarzschildGammaTheta (a b c : Fin 4) : ℝ → ℝ :=
  if a = 1 ∧ b = 3 ∧ c = 3 then fun θ => sin θ ^ 2
  else if a = 2 ∧ b = 3 ∧ c = 3 then fun θ => -(sin θ * cos θ)
  else if a = 3 ∧ ((b = 2 ∧ c = 3) ∨ (b = 3 ∧ c = 2)) then fun θ => cos θ / sin θ
  else fun _ => 1

/-- The `θ`-derivative of `schwarzschildGammaTheta`. -/
def schwarzschildGammaTheta' (a b c : Fin 4) : ℝ → ℝ :=
  if a = 1 ∧ b = 3 ∧ c = 3 then fun θ => 2 * (sin θ * cos θ)
  else if a = 2 ∧ b = 3 ∧ c = 3 then fun θ => sin θ ^ 2 - cos θ ^ 2
  else if a = 3 ∧ ((b = 2 ∧ c = 3) ∨ (b = 3 ∧ c = 2)) then fun θ => -(sin θ ^ 2)⁻¹
  else fun _ => 0

/-!

## C. Derivatives of the Christoffel symbols

-/

section Derivatives

variable {M r θ : ℝ}

lemma hasDerivAt_gammaR_ttr (hr : r ≠ 0) (h2 : r - 2 * M ≠ 0) :
    HasDerivAt (fun r => M / (r * (r - 2 * M)))
      (-(M * (2 * r - 2 * M)) / (r ^ 2 * (r - 2 * M) ^ 2)) r := by
  have := (hasDerivAt_const r M).fun_div
    ((hasDerivAt_id' r).fun_mul ((hasDerivAt_id' r).sub_const (2 * M))) (mul_ne_zero hr h2)
  convert this using 1
  field_simp
  ring

lemma hasDerivAt_gammaR_rtt (hr : r ≠ 0) :
    HasDerivAt (fun r => M * (r - 2 * M) / r ^ 3) (M * (6 * M - 2 * r) / r ^ 4) r := by
  have := (((hasDerivAt_id' r).sub_const (2 * M)).const_mul M).fun_div (hasDerivAt_pow 3 r)
    (pow_ne_zero 3 hr)
  convert this using 1
  field_simp
  push_cast
  ring

lemma hasDerivAt_gammaR_rrr (hr : r ≠ 0) (h2 : r - 2 * M ≠ 0) :
    HasDerivAt (fun r => -(M / (r * (r - 2 * M))))
      (M * (2 * r - 2 * M) / (r ^ 2 * (r - 2 * M) ^ 2)) r := by
  have := (hasDerivAt_gammaR_ttr hr h2).neg
  convert this using 1
  ring

lemma hasDerivAt_gammaR_inv (hr : r ≠ 0) : HasDerivAt (fun r : ℝ => r⁻¹) (-(r ^ 2)⁻¹) r :=
  hasDerivAt_inv hr

lemma hasDerivAt_gammaR_sub : HasDerivAt (fun r : ℝ => -(r - 2 * M)) (-1) r :=
  ((hasDerivAt_id r).sub_const (2 * M)).neg

lemma hasDerivAt_gammaR (hr : r ≠ 0) (h2 : r - 2 * M ≠ 0) (a b c : Fin 4) :
    HasDerivAt (schwarzschildGammaR M a b c) (schwarzschildGammaR' M a b c r) r := by
  unfold schwarzschildGammaR schwarzschildGammaR'
  split_ifs
  · exact hasDerivAt_gammaR_ttr hr h2
  · exact hasDerivAt_gammaR_rtt hr
  · exact hasDerivAt_gammaR_rrr hr h2
  · exact hasDerivAt_gammaR_sub
  · exact hasDerivAt_gammaR_inv hr
  · exact hasDerivAt_const _ _
  · exact hasDerivAt_const _ _

lemma hasDerivAt_gammaTheta (hθ : sin θ ≠ 0) (a b c : Fin 4) :
    HasDerivAt (schwarzschildGammaTheta a b c) (schwarzschildGammaTheta' a b c θ) θ := by
  unfold schwarzschildGammaTheta schwarzschildGammaTheta'
  split_ifs
  · have := (hasDerivAt_sin θ).fun_pow 2
    convert this using 1
    simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
    ring
  · have := ((hasDerivAt_sin θ).fun_mul (hasDerivAt_cos θ)).neg
    convert this using 1
    simp only [mul_neg, neg_add_rev, neg_neg]
    ring
  · have := (hasDerivAt_cos θ).fun_div (hasDerivAt_sin θ) hθ
    convert this using 1
    field_simp
    nlinarith [sin_sq_add_cos_sq θ]
  · exact hasDerivAt_const _ _

end Derivatives


/-!

## D. Derivatives of the metric

-/

section Entries

variable {M : ℝ} {x : Fin 4 → ℝ} {b p q : Fin 4}

lemma coordDeriv_schwarzschildMetric_tt (hM : 0 < M) (hx : x ∈ schwarzschildDomain M) (b : Fin 4) :
    coordDeriv (fun y => schwarzschildMetric M y 0 0) x b
      = if b = 1 then -(2 * M / x 1 ^ 2) else 0 := by
  have h1 := (schwarzschildDomain.pos hM hx).ne'
  have hA : HasDerivAt (fun r : ℝ => -(1 - 2 * M / r)) (-(2 * M / x 1 ^ 2)) (x 1) := by
    have := ((hasDerivAt_const (x 1) (1 : ℝ)).sub
      ((hasDerivAt_const (x 1) (2 * M)).fun_div (hasDerivAt_id' (x 1)) h1)).neg
    convert this using 1
    field_simp
    simp
  have : (fun y => schwarzschildMetric M y 0 0)
      = fun y => (fun r : ℝ => -(1 - 2 * M / r)) (y 1) := by
    funext y; simp [schwarzschildMetric]
  rw [this, coordDeriv_comp_proj 1 hA.differentiableAt, hA.deriv]

lemma coordDeriv_schwarzschildMetric_rr (hM : 0 < M) (hx : x ∈ schwarzschildDomain M) (b : Fin 4) :
    coordDeriv (fun y => schwarzschildMetric M y 1 1) x b
      = if b = 1 then -((2 * M / x 1 ^ 2) / (1 - 2 * M / x 1) ^ 2) else 0 := by
  have h1 := (schwarzschildDomain.pos hM hx).ne'
  have h2 := (schwarzschildDomain.one_sub_pos hM hx).ne'
  have hA : HasDerivAt (fun r : ℝ => (1 - 2 * M / r)⁻¹)
      (-((2 * M / x 1 ^ 2) / (1 - 2 * M / x 1) ^ 2)) (x 1) := by
    have := ((hasDerivAt_const (x 1) (1 : ℝ)).sub
      ((hasDerivAt_const (x 1) (2 * M)).fun_div (hasDerivAt_id' (x 1)) h1)).inv h2
    have h3 : x 1 - 2 * M ≠ 0 := (schwarzschildDomain.sub_pos hx).ne'
    convert this using 1
    simp only [Pi.sub_apply]
    field_simp
    ring
  have : (fun y => schwarzschildMetric M y 1 1)
      = fun y => (fun r : ℝ => (1 - 2 * M / r)⁻¹) (y 1) := by
    funext y; simp [schwarzschildMetric]
  rw [this, coordDeriv_comp_proj 1 hA.differentiableAt, hA.deriv]

lemma coordDeriv_schwarzschildMetric_θθ (b : Fin 4) :
    coordDeriv (fun y => schwarzschildMetric M y 2 2) x b = if b = 1 then 2 * x 1 else 0 := by
  have hA : HasDerivAt (fun r : ℝ => r ^ 2) (2 * x 1) (x 1) := by
    simpa using hasDerivAt_pow 2 (x 1)
  have : (fun y => schwarzschildMetric M y 2 2) = fun y => (fun r : ℝ => r ^ 2) (y 1) := by
    funext y; simp [schwarzschildMetric]
  rw [this, coordDeriv_comp_proj 1 hA.differentiableAt, hA.deriv]

lemma coordDeriv_schwarzschildMetric_φφ (b : Fin 4) :
    coordDeriv (fun y => schwarzschildMetric M y 3 3) x b
      = (if b = 1 then 2 * x 1 else 0) * sin (x 2) ^ 2
        + x 1 ^ 2 * (if b = 2 then 2 * (sin (x 2) * cos (x 2)) else 0) := by
  have hA : HasDerivAt (fun r : ℝ => r ^ 2) (2 * x 1) (x 1) := by
    simpa using hasDerivAt_pow 2 (x 1)
  have hB : HasDerivAt (fun θ : ℝ => sin θ ^ 2) (2 * (sin (x 2) * cos (x 2))) (x 2) := by
    simpa [mul_assoc] using (hasDerivAt_sin (x 2)).fun_pow 2
  have : (fun y => schwarzschildMetric M y 3 3)
      = fun y => (fun r : ℝ => r ^ 2) (y 1) * (fun θ : ℝ => sin θ ^ 2) (y 2) := by
    funext y; simp [schwarzschildMetric]
  rw [this, coordDeriv_proj_mul 1 2 hA.differentiableAt hB.differentiableAt, hA.deriv, hB.deriv]

lemma coordDeriv_schwarzschildMetric_offDiag (hpq : p ≠ q) :
    coordDeriv (fun y => schwarzschildMetric M y p q) x b = 0 := by
  simp [schwarzschildMetric, Matrix.diagonal_apply_ne _ hpq, coordDeriv]

lemma schwarzschildMetric_inv (hM : 0 < M) {y : Fin 4 → ℝ} (hy : y ∈ schwarzschildDomain M) :
    (schwarzschildMetric M y)⁻¹ = Matrix.diagonal
      ![-(1 - 2 * M / y 1)⁻¹, 1 - 2 * M / y 1, (y 1 ^ 2)⁻¹, (y 1 ^ 2 * sin (y 2) ^ 2)⁻¹] := by
  have h1 := (schwarzschildDomain.pos hM hy).ne'
  have h3 := (schwarzschildDomain.sin_pos hy).ne'
  have h4 := (schwarzschildDomain.one_sub_pos hM hy).ne'
  have h5 := (schwarzschildDomain.sub_pos hy).ne'
  refine Matrix.inv_eq_right_inv ?_
  rw [schwarzschildMetric, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp <;> field_simp
  ring

end Entries

/-!

## E. The Christoffel symbols

-/

/-- The Christoffel symbols of the Schwarzschild metric on the exterior region. -/
lemma christoffel_schwarzschild {M : ℝ} {x : Fin 4 → ℝ} (hM : 0 < M)
    (hx : x ∈ schwarzschildDomain M) (a b c : Fin 4) :
    christoffel (schwarzschildMetric M) x a b c
      = schwarzschildGammaR M a b c (x 1) * schwarzschildGammaTheta a b c (x 2) := by
  have h1 := (schwarzschildDomain.pos hM hx).ne'
  have h2 := (schwarzschildDomain.sub_pos hx).ne'
  have h3 := (schwarzschildDomain.sin_pos hx).ne'
  have h4 := (schwarzschildDomain.one_sub_pos hM hx).ne'
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
  simp [christoffel, christoffelFirstKind, schwarzschildMetric_inv hM hx,
    Matrix.diagonal_apply, coordDeriv_schwarzschildMetric_tt hM hx,
    coordDeriv_schwarzschildMetric_rr hM hx,
    coordDeriv_schwarzschildMetric_θθ, coordDeriv_schwarzschildMetric_φφ,
    coordDeriv_schwarzschildMetric_offDiag, schwarzschildGammaR, schwarzschildGammaTheta]
  all_goals first | (field_simp; ring) | field_simp

end GeneralRelativity
