/-
Copyright (c) 2026 Harsha Vankayalapati. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harsha Vankayalapati
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Physlib.Relativity.SpeedOfLight
public import PhyslibAlpha.Relativity.General.Curvature

/-!

# The Schwarzschild metric and its Christoffel symbols

The Schwarzschild metric in Schwarzschild coordinates on the exterior region `r > 2GM/c²`.

## i. Overview

In coordinates `(t, r, θ, φ)`, with `t` a time, the Schwarzschild metric of a mass `M` is, in the
signature `(+,-,-,-)`,
`c² (1 - r_s/r) dt² - (1 - r_s/r)⁻¹ dr² - r² dθ² - r² sin²θ dφ²`,
where `r_s = 2GM/c²` is the Schwarzschild radius (`schwarzschildRadius`), `G : ℝ` is Newton's
constant and `c : SpeedOfLight` is the speed of light; take `c = 1` for units in which it is one.
It is a Lorentzian metric field on the region `r_s < r`, `0 < θ < π`
(`isLorentzianMetricOn_schwarzschildMetric`). We compute all its Christoffel symbols
(`christoffel_schwarzschild`). Each one is a product of a function of `r` and a function of `θ`
(`schwarzschildGammaR`, `schwarzschildGammaTheta`), whose derivatives are recorded in
`hasDerivAt_gammaR` and `hasDerivAt_gammaTheta`.

## ii. Key results

- `schwarzschildRadius` : the Schwarzschild radius `2GM/c²`.
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
- L. D. Landau and E. M. Lifshitz, *The Classical Theory of Fields*, Section 100 (the metric with
  `G` and `c`, in the signature `(+,-,-,-)`).
- R. M. Wald, *General Relativity*, Chapter 6 (in the opposite sign convention `(-,+,+,+)` and
  units with `G = c = 1`).

-/

@[expose] public section

noncomputable section

namespace GeneralRelativity

open Real

/-!

## A. The metric

-/

/-- The Schwarzschild radius `r_s = 2GM/c²` of a mass `M`.

- `G : ℝ` is Newton's constant.
- `c : SpeedOfLight` is the speed of light; take `c = 1` for units in which it is one.
- `M : ℝ` is the mass. -/
def schwarzschildRadius (G : ℝ) (c : SpeedOfLight) (M : ℝ) : ℝ := 2 * G * M / (c : ℝ) ^ 2

/-- The Schwarzschild radius of a positive mass is positive. -/
lemma schwarzschildRadius_pos {G : ℝ} {c : SpeedOfLight} {M : ℝ} (hG : 0 < G) (hM : 0 < M) :
    0 < schwarzschildRadius G c M :=
  div_pos (by positivity) (pow_pos c.val_pos 2)

/-- The Schwarzschild metric
`c² (1 - r_s/r) dt² - (1 - r_s/r)⁻¹ dr² - r² dθ² - r² sin²θ dφ²`, with `r_s = 2GM/c²`, in
Schwarzschild coordinates `(t, r, θ, φ)` and the signature `(+,-,-,-)`.

- `G : ℝ` is Newton's constant.
- `c : SpeedOfLight` is the speed of light; take `c = 1` for units in which it is one.
- `M : ℝ` is the mass. -/
def schwarzschildMetric (G : ℝ) (c : SpeedOfLight) (M : ℝ) :
    (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ :=
  fun y => Matrix.diagonal ![(c : ℝ) ^ 2 * (1 - schwarzschildRadius G c M / y 1),
    -(1 - schwarzschildRadius G c M / y 1)⁻¹, -y 1 ^ 2, -(y 1 ^ 2 * sin (y 2) ^ 2)]

/-- The exterior region `r > 2GM/c²` with `0 < θ < π`, on which the coordinates are regular. -/
def schwarzschildDomain (G : ℝ) (c : SpeedOfLight) (M : ℝ) : Set (Fin 4 → ℝ) :=
  {y | schwarzschildRadius G c M < y 1 ∧ 0 < y 2 ∧ y 2 < π}

lemma isOpen_schwarzschildDomain (G : ℝ) (c : SpeedOfLight) (M : ℝ) :
    IsOpen (schwarzschildDomain G c M) :=
  (isOpen_lt continuous_const (continuous_apply 1)).inter
    ((isOpen_lt continuous_const (continuous_apply 2)).inter
      (isOpen_lt (continuous_apply 2) continuous_const))

section Domain

variable {G : ℝ} {c : SpeedOfLight} {M : ℝ} {x : Fin 4 → ℝ}

lemma schwarzschildDomain.pos (hG : 0 < G) (hM : 0 < M) (hx : x ∈ schwarzschildDomain G c M) :
    0 < x 1 :=
  (schwarzschildRadius_pos hG hM).trans hx.1

lemma schwarzschildDomain.sub_pos (hx : x ∈ schwarzschildDomain G c M) :
    0 < x 1 - schwarzschildRadius G c M := by
  have := hx.1; linarith

lemma schwarzschildDomain.sin_pos (hx : x ∈ schwarzschildDomain G c M) : 0 < sin (x 2) :=
  Real.sin_pos_of_pos_of_lt_pi hx.2.1 hx.2.2

lemma schwarzschildDomain.one_sub_pos (hG : 0 < G) (hM : 0 < M)
    (hx : x ∈ schwarzschildDomain G c M) : 0 < 1 - schwarzschildRadius G c M / x 1 := by
  have h1 := schwarzschildDomain.pos hG hM hx
  have h2 := schwarzschildDomain.sub_pos hx
  have : 1 - schwarzschildRadius G c M / x 1 = (x 1 - schwarzschildRadius G c M) / x 1 := by
    field_simp
  rw [this]; positivity

/-- The Schwarzschild metric is a Lorentzian metric on the exterior region. -/
lemma isLorentzianMetricOn_schwarzschildMetric (hG : 0 < G) (hM : 0 < M) :
    IsLorentzianMetricOn (schwarzschildMetric G c M) (schwarzschildDomain G c M) where
  isOpen := isOpen_schwarzschildDomain G c M
  symm _ _ := Matrix.isSymm_diagonal _
  contDiffOn a b := by
    unfold schwarzschildMetric
    intro y hy
    have h1 := schwarzschildDomain.pos hG hM hy
    have h2 := schwarzschildDomain.one_sub_pos hG hM hy
    by_cases hab : a = b
    · subst hab
      refine ContDiffAt.contDiffWithinAt ?_
      fin_cases a <;> simp [Matrix.diagonal_apply_eq]
      · fun_prop (disch := positivity)
      · exact ContDiffAt.neg (ContDiffAt.inv (by fun_prop (disch := positivity)) h2.ne')
      · fun_prop
      · fun_prop
    · simp [Matrix.diagonal_apply_ne _ hab]
      exact contDiffWithinAt_const
  lorentzian y hy := by
    have h1 := schwarzschildDomain.pos hG hM hy
    have h2 := schwarzschildDomain.one_sub_pos hG hM hy
    have h3 := schwarzschildDomain.sin_pos hy
    refine isLorentzian_diagonal_four ?_ ?_ ?_ ?_
    · exact mul_pos (pow_pos c.val_pos 2) h2
    · exact neg_neg_of_pos (inv_pos.mpr h2)
    · exact neg_neg_of_pos (pow_pos h1 2)
    · exact neg_neg_of_pos (mul_pos (pow_pos h1 2) (pow_pos h3 2))

end Domain


/-!

## B. Closed form of the Christoffel symbols

-/

/-- The `r`-dependent factor of the Christoffel symbol `Γ^a_{ij}` of the Schwarzschild metric,
with `r_s = 2GM/c²`: `Γ^t_{tr} = r_s / (2 r (r - r_s))`, `Γ^r_{tt} = c² r_s (r - r_s) / (2 r³)`,
`Γ^r_{rr} = -r_s / (2 r (r - r_s))`, `Γ^r_{θθ} = -(r - r_s)`, `Γ^θ_{rθ} = 1 / r`. -/
def schwarzschildGammaR (G : ℝ) (c : SpeedOfLight) (M : ℝ) (a i j : Fin 4) : ℝ → ℝ :=
  if a = 0 ∧ ((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)) then
    fun r => schwarzschildRadius G c M / (2 * r * (r - schwarzschildRadius G c M))
  else if a = 1 ∧ i = 0 ∧ j = 0 then
    fun r => (c : ℝ) ^ 2 * schwarzschildRadius G c M * (r - schwarzschildRadius G c M) / (2 * r ^ 3)
  else if a = 1 ∧ i = 1 ∧ j = 1 then
    fun r => -(schwarzschildRadius G c M / (2 * r * (r - schwarzschildRadius G c M)))
  else if a = 1 ∧ ((i = 2 ∧ j = 2) ∨ (i = 3 ∧ j = 3)) then
    fun r => -(r - schwarzschildRadius G c M)
  else if (a = 2 ∨ a = 3) ∧ ((i = 1 ∧ j = a) ∨ (i = a ∧ j = 1)) then fun r => r⁻¹
  else if (a = 2 ∧ i = 3 ∧ j = 3) ∨ (a = 3 ∧ ((i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2))) then
    fun _ => 1
  else fun _ => 0

/-- The `r`-derivative of `schwarzschildGammaR`. -/
def schwarzschildGammaR' (G : ℝ) (c : SpeedOfLight) (M : ℝ) (a i j : Fin 4) : ℝ → ℝ :=
  if a = 0 ∧ ((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)) then
    fun r => -(schwarzschildRadius G c M * (2 * r - schwarzschildRadius G c M))
      / (2 * r ^ 2 * (r - schwarzschildRadius G c M) ^ 2)
  else if a = 1 ∧ i = 0 ∧ j = 0 then
    fun r => (c : ℝ) ^ 2 * schwarzschildRadius G c M * (3 * schwarzschildRadius G c M - 2 * r)
      / (2 * r ^ 4)
  else if a = 1 ∧ i = 1 ∧ j = 1 then
    fun r => schwarzschildRadius G c M * (2 * r - schwarzschildRadius G c M)
      / (2 * r ^ 2 * (r - schwarzschildRadius G c M) ^ 2)
  else if a = 1 ∧ ((i = 2 ∧ j = 2) ∨ (i = 3 ∧ j = 3)) then fun _ => -1
  else if (a = 2 ∨ a = 3) ∧ ((i = 1 ∧ j = a) ∨ (i = a ∧ j = 1)) then fun r => -(r ^ 2)⁻¹
  else fun _ => 0

/-- The `θ`-dependent factor of the Christoffel symbol `Γ^a_{ij}` of the Schwarzschild metric. -/
def schwarzschildGammaTheta (a i j : Fin 4) : ℝ → ℝ :=
  if a = 1 ∧ i = 3 ∧ j = 3 then fun θ => sin θ ^ 2
  else if a = 2 ∧ i = 3 ∧ j = 3 then fun θ => -(sin θ * cos θ)
  else if a = 3 ∧ ((i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2)) then fun θ => cos θ / sin θ
  else fun _ => 1

/-- The `θ`-derivative of `schwarzschildGammaTheta`. -/
def schwarzschildGammaTheta' (a i j : Fin 4) : ℝ → ℝ :=
  if a = 1 ∧ i = 3 ∧ j = 3 then fun θ => 2 * (sin θ * cos θ)
  else if a = 2 ∧ i = 3 ∧ j = 3 then fun θ => sin θ ^ 2 - cos θ ^ 2
  else if a = 3 ∧ ((i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2)) then fun θ => -(sin θ ^ 2)⁻¹
  else fun _ => 0

/-!

## C. Derivatives of the Christoffel symbols

In this section `rs` stands for the Schwarzschild radius and `κ` for `c²`.

-/

section Derivatives

variable {rs κ r θ : ℝ}

lemma hasDerivAt_gammaR_ttr (hr : r ≠ 0) (h2 : r - rs ≠ 0) :
    HasDerivAt (fun r => rs / (2 * r * (r - rs)))
      (-(rs * (2 * r - rs)) / (2 * r ^ 2 * (r - rs) ^ 2)) r := by
  have := (hasDerivAt_const r rs).fun_div
    (((hasDerivAt_id' r).const_mul 2).fun_mul ((hasDerivAt_id' r).sub_const rs))
    (mul_ne_zero (mul_ne_zero two_ne_zero hr) h2)
  convert this using 1
  field_simp
  ring

lemma hasDerivAt_gammaR_rtt (hr : r ≠ 0) :
    HasDerivAt (fun r => κ * rs * (r - rs) / (2 * r ^ 3)) (κ * rs * (3 * rs - 2 * r) / (2 * r ^ 4))
      r := by
  have := (((hasDerivAt_id' r).sub_const rs).const_mul (κ * rs)).fun_div
    ((hasDerivAt_pow 3 r).const_mul 2) (mul_ne_zero two_ne_zero (pow_ne_zero 3 hr))
  convert this using 1
  field_simp
  push_cast
  ring

lemma hasDerivAt_gammaR_rrr (hr : r ≠ 0) (h2 : r - rs ≠ 0) :
    HasDerivAt (fun r => -(rs / (2 * r * (r - rs))))
      (rs * (2 * r - rs) / (2 * r ^ 2 * (r - rs) ^ 2)) r := by
  have := (hasDerivAt_gammaR_ttr hr h2).neg
  convert this using 1
  ring

lemma hasDerivAt_gammaR_inv (hr : r ≠ 0) : HasDerivAt (fun r : ℝ => r⁻¹) (-(r ^ 2)⁻¹) r :=
  hasDerivAt_inv hr

lemma hasDerivAt_gammaR_sub : HasDerivAt (fun r : ℝ => -(r - rs)) (-1) r :=
  ((hasDerivAt_id r).sub_const rs).neg

lemma hasDerivAt_gammaR {G : ℝ} {c : SpeedOfLight} {M : ℝ} (hr : r ≠ 0)
    (h2 : r - schwarzschildRadius G c M ≠ 0) (a i j : Fin 4) :
    HasDerivAt (schwarzschildGammaR G c M a i j) (schwarzschildGammaR' G c M a i j r) r := by
  unfold schwarzschildGammaR schwarzschildGammaR'
  split_ifs
  · exact hasDerivAt_gammaR_ttr hr h2
  · exact hasDerivAt_gammaR_rtt hr
  · exact hasDerivAt_gammaR_rrr hr h2
  · exact hasDerivAt_gammaR_sub
  · exact hasDerivAt_gammaR_inv hr
  · exact hasDerivAt_const _ _
  · exact hasDerivAt_const _ _

lemma hasDerivAt_gammaTheta (hθ : sin θ ≠ 0) (a i j : Fin 4) :
    HasDerivAt (schwarzschildGammaTheta a i j) (schwarzschildGammaTheta' a i j θ) θ := by
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

variable {G : ℝ} {c : SpeedOfLight} {M : ℝ} {x : Fin 4 → ℝ} {p q : Fin 4}

lemma coordDeriv_schwarzschildMetric_tt (hG : 0 < G) (hM : 0 < M)
    (hx : x ∈ schwarzschildDomain G c M) (j : Fin 4) :
    coordDeriv (fun y => schwarzschildMetric G c M y 0 0) x j
      = if j = 1 then (c : ℝ) ^ 2 * (schwarzschildRadius G c M / x 1 ^ 2) else 0 := by
  have h1 := (schwarzschildDomain.pos hG hM hx).ne'
  have hA : HasDerivAt (fun r : ℝ => (c : ℝ) ^ 2 * (1 - schwarzschildRadius G c M / r))
      ((c : ℝ) ^ 2 * (schwarzschildRadius G c M / x 1 ^ 2)) (x 1) := by
    have := ((hasDerivAt_const (x 1) (1 : ℝ)).sub
      ((hasDerivAt_const (x 1) (schwarzschildRadius G c M)).fun_div (hasDerivAt_id' (x 1))
        h1)).const_mul ((c : ℝ) ^ 2)
    convert this using 1
    field_simp
    simp
  have : (fun y => schwarzschildMetric G c M y 0 0)
      = fun y => (fun r : ℝ => (c : ℝ) ^ 2 * (1 - schwarzschildRadius G c M / r)) (y 1) := by
    funext y; simp [schwarzschildMetric]
  rw [this, coordDeriv_comp_proj 1 hA.differentiableAt, hA.deriv]

lemma coordDeriv_schwarzschildMetric_rr (hG : 0 < G) (hM : 0 < M)
    (hx : x ∈ schwarzschildDomain G c M) (j : Fin 4) :
    coordDeriv (fun y => schwarzschildMetric G c M y 1 1) x j
      = if j = 1 then (schwarzschildRadius G c M / x 1 ^ 2)
          / (1 - schwarzschildRadius G c M / x 1) ^ 2 else 0 := by
  have h1 := (schwarzschildDomain.pos hG hM hx).ne'
  have h2 := (schwarzschildDomain.one_sub_pos hG hM hx).ne'
  have hA : HasDerivAt (fun r : ℝ => -(1 - schwarzschildRadius G c M / r)⁻¹)
      ((schwarzschildRadius G c M / x 1 ^ 2) / (1 - schwarzschildRadius G c M / x 1) ^ 2)
      (x 1) := by
    have := (((hasDerivAt_const (x 1) (1 : ℝ)).sub
      ((hasDerivAt_const (x 1) (schwarzschildRadius G c M)).fun_div (hasDerivAt_id' (x 1))
        h1)).inv h2).neg
    have h3 : x 1 - schwarzschildRadius G c M ≠ 0 := (schwarzschildDomain.sub_pos hx).ne'
    convert this using 1
    simp only [Pi.sub_apply]
    field_simp
    ring
  have : (fun y => schwarzschildMetric G c M y 1 1)
      = fun y => (fun r : ℝ => -(1 - schwarzschildRadius G c M / r)⁻¹) (y 1) := by
    funext y; simp [schwarzschildMetric]
  rw [this, coordDeriv_comp_proj 1 hA.differentiableAt, hA.deriv]

lemma coordDeriv_schwarzschildMetric_θθ (j : Fin 4) :
    coordDeriv (fun y => schwarzschildMetric G c M y 2 2) x j
      = if j = 1 then -(2 * x 1) else 0 := by
  have hA : HasDerivAt (fun r : ℝ => -r ^ 2) (-(2 * x 1)) (x 1) :=
    (by simpa using hasDerivAt_pow 2 (x 1) : HasDerivAt (fun r : ℝ => r ^ 2) (2 * x 1) (x 1)).neg
  have : (fun y => schwarzschildMetric G c M y 2 2) = fun y => (fun r : ℝ => -r ^ 2) (y 1) := by
    funext y; simp [schwarzschildMetric]
  rw [this, coordDeriv_comp_proj 1 hA.differentiableAt, hA.deriv]

lemma coordDeriv_schwarzschildMetric_φφ (j : Fin 4) :
    coordDeriv (fun y => schwarzschildMetric G c M y 3 3) x j
      = (if j = 1 then -(2 * x 1) else 0) * sin (x 2) ^ 2
        + -x 1 ^ 2 * (if j = 2 then 2 * (sin (x 2) * cos (x 2)) else 0) := by
  have hA : HasDerivAt (fun r : ℝ => -r ^ 2) (-(2 * x 1)) (x 1) :=
    (by simpa using hasDerivAt_pow 2 (x 1) : HasDerivAt (fun r : ℝ => r ^ 2) (2 * x 1) (x 1)).neg
  have hB : HasDerivAt (fun θ : ℝ => sin θ ^ 2) (2 * (sin (x 2) * cos (x 2))) (x 2) := by
    simpa [mul_assoc] using (hasDerivAt_sin (x 2)).fun_pow 2
  have : (fun y => schwarzschildMetric G c M y 3 3)
      = fun y => (fun r : ℝ => -r ^ 2) (y 1) * (fun θ : ℝ => sin θ ^ 2) (y 2) := by
    funext y; simp [schwarzschildMetric]
  rw [this, coordDeriv_proj_mul 1 2 hA.differentiableAt hB.differentiableAt, hA.deriv, hB.deriv]

lemma coordDeriv_schwarzschildMetric_offDiag {j : Fin 4} (hpq : p ≠ q) :
    coordDeriv (fun y => schwarzschildMetric G c M y p q) x j = 0 := by
  simp [schwarzschildMetric, Matrix.diagonal_apply_ne _ hpq, coordDeriv]

lemma schwarzschildMetric_inv (hG : 0 < G) (hM : 0 < M) {y : Fin 4 → ℝ}
    (hy : y ∈ schwarzschildDomain G c M) :
    (schwarzschildMetric G c M y)⁻¹ = Matrix.diagonal
      ![((c : ℝ) ^ 2 * (1 - schwarzschildRadius G c M / y 1))⁻¹,
        -(1 - schwarzschildRadius G c M / y 1), -(y 1 ^ 2)⁻¹, -(y 1 ^ 2 * sin (y 2) ^ 2)⁻¹] := by
  have h1 := (schwarzschildDomain.pos hG hM hy).ne'
  have h3 := (schwarzschildDomain.sin_pos hy).ne'
  have h4 := (schwarzschildDomain.one_sub_pos hG hM hy).ne'
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
lemma christoffel_schwarzschild {G : ℝ} {c : SpeedOfLight} {M : ℝ} {x : Fin 4 → ℝ} (hG : 0 < G)
    (hM : 0 < M) (hx : x ∈ schwarzschildDomain G c M) (a i j : Fin 4) :
    christoffel (schwarzschildMetric G c M) x a i j
      = schwarzschildGammaR G c M a i j (x 1) * schwarzschildGammaTheta a i j (x 2) := by
  have h1 := (schwarzschildDomain.pos hG hM hx).ne'
  have h2 := (schwarzschildDomain.sub_pos hx).ne'
  have h3 := (schwarzschildDomain.sin_pos hx).ne'
  have h4 := (schwarzschildDomain.one_sub_pos hG hM hx).ne'
  fin_cases a <;> fin_cases i <;> fin_cases j <;>
  simp [christoffel, christoffelFirstKind, schwarzschildMetric_inv hG hM hx,
    Matrix.diagonal_apply, coordDeriv_schwarzschildMetric_tt hG hM hx,
    coordDeriv_schwarzschildMetric_rr hG hM hx,
    coordDeriv_schwarzschildMetric_θθ, coordDeriv_schwarzschildMetric_φφ,
    coordDeriv_schwarzschildMetric_offDiag, schwarzschildGammaR, schwarzschildGammaTheta]
  all_goals first | (field_simp; ring) | field_simp

end GeneralRelativity
