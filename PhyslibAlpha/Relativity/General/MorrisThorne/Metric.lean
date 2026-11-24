/-
Copyright (c) 2026 Harsha Vankayalapati. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harsha Vankayalapati
-/
module

public import PhyslibAlpha.Relativity.General.Schwarzschild.Metric

/-!

# The Morris-Thorne wormhole metric and its Christoffel symbols

The static spherically symmetric Morris-Thorne metric with zero redshift function and arbitrary
shape function `b`.

## i. Overview

In coordinates `(t, r, θ, φ)` and units `G = c = 1` the Morris-Thorne wormhole metric with zero
redshift function and shape function `b` is
`-dt² + (1 - b(r)/r)⁻¹ dr² + r² dθ² + r² sin²θ dφ²`.
It is a Lorentzian metric field on the region `0 < r`, `b(r) < r`, `0 < θ < π`
(`isLorentzianMetricOn_morrisThorneMetric`), for any smooth `b`. A *throat* is a radius `r₀`
with `b(r₀) = r₀`, where the coordinate `r` stops being a good coordinate; the metric is
considered on the region `r > b(r)` outside the throat.

We compute all Christoffel symbols (`christoffel_morrisThorne`). Each one is a product of a
function of `r` (`morrisThorneGammaR`) and a function of `θ` (`schwarzschildGammaTheta`, which is
the same as for the Schwarzschild metric), and the derivative of the former is recorded in
`hasDerivAt_morrisThorneGammaR`.

## ii. Key results

- `morrisThorneMetric` : the metric field.
- `morrisThorneDomain` : the region `0 < r`, `b(r) < r`, `0 < θ < π`.
- `isLorentzianMetricOn_morrisThorneMetric` : it is a Lorentzian metric on that region.
- `morrisThorneMetric_inv` : the inverse metric.
- `christoffel_morrisThorne` : the Christoffel symbols.

## iii. Table of contents

- A. The metric
- B. Closed form of the Christoffel symbols
- C. Derivatives of the Christoffel symbols
- D. Derivatives of the metric
- E. The Christoffel symbols

## iv. References

- M. S. Morris and K. S. Thorne, *Wormholes in spacetime and their use for interstellar travel:
  A tool for teaching general relativity*, Am. J. Phys. 56, 395 (1988).

-/

@[expose] public section

noncomputable section

namespace GeneralRelativity

open Real
open scoped ContDiff

/-!

## A. The metric

-/

/-- The Morris-Thorne metric `-dt² + (1 - b(r)/r)⁻¹ dr² + r² dθ² + r² sin²θ dφ²` with zero
redshift function and shape function `b`, in coordinates `(t, r, θ, φ)` and units `G = c = 1`. -/
def morrisThorneMetric (b : ℝ → ℝ) : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ :=
  fun y => Matrix.diagonal ![-1, (1 - b (y 1) / y 1)⁻¹, y 1 ^ 2, y 1 ^ 2 * sin (y 2) ^ 2]

/-- The region `0 < r`, `b(r) < r`, `0 < θ < π` on which the Morris-Thorne coordinates are
regular. -/
def morrisThorneDomain (b : ℝ → ℝ) : Set (Fin 4 → ℝ) :=
  {y | 0 < y 1 ∧ b (y 1) < y 1 ∧ 0 < y 2 ∧ y 2 < π}

lemma isOpen_morrisThorneDomain {b : ℝ → ℝ} (hb : Continuous b) :
    IsOpen (morrisThorneDomain b) :=
  (isOpen_lt continuous_const (continuous_apply 1)).inter
    ((isOpen_lt (hb.comp (continuous_apply 1)) (continuous_apply 1)).inter
      ((isOpen_lt continuous_const (continuous_apply 2)).inter
        (isOpen_lt (continuous_apply 2) continuous_const)))

section Domain

variable {b : ℝ → ℝ} {x : Fin 4 → ℝ}

lemma morrisThorneDomain.pos (hx : x ∈ morrisThorneDomain b) : 0 < x 1 := hx.1

lemma morrisThorneDomain.sub_pos (hx : x ∈ morrisThorneDomain b) : 0 < x 1 - b (x 1) := by
  have := hx.2.1; linarith

lemma morrisThorneDomain.sin_pos (hx : x ∈ morrisThorneDomain b) : 0 < sin (x 2) :=
  Real.sin_pos_of_pos_of_lt_pi hx.2.2.1 hx.2.2.2

lemma morrisThorneDomain.one_sub_pos (hx : x ∈ morrisThorneDomain b) :
    0 < 1 - b (x 1) / x 1 := by
  have h1 := morrisThorneDomain.pos hx
  have h2 := morrisThorneDomain.sub_pos hx
  have : 1 - b (x 1) / x 1 = (x 1 - b (x 1)) / x 1 := by field_simp
  rw [this]; positivity

/-- The Morris-Thorne metric is a Lorentzian metric on the region outside the throat. -/
lemma isLorentzianMetricOn_morrisThorneMetric (hb : ContDiff ℝ ∞ b) :
    IsLorentzianMetricOn (morrisThorneMetric b) (morrisThorneDomain b) where
  isOpen := isOpen_morrisThorneDomain hb.continuous
  symm _ _ := Matrix.isSymm_diagonal _
  contDiffOn a c := by
    unfold morrisThorneMetric
    intro y hy
    have h1 := morrisThorneDomain.pos hy
    have h2 := morrisThorneDomain.one_sub_pos hy
    have hbr : ContDiffAt ℝ ∞ (fun y : Fin 4 → ℝ => b (y 1)) y :=
      (hb.comp (by fun_prop : ContDiff ℝ ∞ fun y : Fin 4 → ℝ => y 1)).contDiffAt
    by_cases hac : a = c
    · subst hac
      refine ContDiffAt.contDiffWithinAt ?_
      fin_cases a <;> simp [Matrix.diagonal_apply_eq]
      · exact contDiffAt_const
      · exact ContDiffAt.inv (contDiffAt_const.sub (hbr.div
          (by fun_prop : ContDiffAt ℝ ∞ (fun y : Fin 4 → ℝ => y 1) y) h1.ne')) h2.ne'
      · fun_prop
      · fun_prop
    · simp [Matrix.diagonal_apply_ne _ hac]
      exact contDiffWithinAt_const
  lorentzian y hy := by
    have h1 := morrisThorneDomain.pos hy
    have h2 := morrisThorneDomain.one_sub_pos hy
    have h3 := morrisThorneDomain.sin_pos hy
    refine isLorentzian_diagonal_four ?_ ?_ ?_ ?_
    · simp
    · simpa using h2
    · show (0 : ℝ) < y 1 ^ 2
      positivity
    · simp; positivity

end Domain

/-!

## B. Closed form of the Christoffel symbols

-/

/-- The `r`-dependent factor of the Christoffel symbol `Γ^a_{ij}` of the Morris-Thorne metric.
The `θ`-dependent factor is `schwarzschildGammaTheta a i j`. -/
def morrisThorneGammaR (b : ℝ → ℝ) (a i j : Fin 4) : ℝ → ℝ :=
  if a = 1 ∧ i = 1 ∧ j = 1 then fun r => (r * deriv b r - b r) / (2 * r * (r - b r))
  else if a = 1 ∧ ((i = 2 ∧ j = 2) ∨ (i = 3 ∧ j = 3)) then fun r => -(r - b r)
  else if (a = 2 ∨ a = 3) ∧ ((i = 1 ∧ j = a) ∨ (i = a ∧ j = 1)) then fun r => r⁻¹
  else if (a = 2 ∧ i = 3 ∧ j = 3) ∨ (a = 3 ∧ ((i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2))) then
    fun _ => 1
  else fun _ => 0

/-- The `r`-derivative of `morrisThorneGammaR`. -/
def morrisThorneGammaR' (b : ℝ → ℝ) (a i j : Fin 4) : ℝ → ℝ :=
  if a = 1 ∧ i = 1 ∧ j = 1 then
    fun r => (r * deriv (deriv b) r * (2 * r * (r - b r))
      - (r * deriv b r - b r) * (2 * (r - b r) + 2 * r * (1 - deriv b r)))
      / (2 * r * (r - b r)) ^ 2
  else if a = 1 ∧ ((i = 2 ∧ j = 2) ∨ (i = 3 ∧ j = 3)) then fun r => -(1 - deriv b r)
  else if (a = 2 ∨ a = 3) ∧ ((i = 1 ∧ j = a) ∨ (i = a ∧ j = 1)) then fun r => -(r ^ 2)⁻¹
  else fun _ => 0

/-!

## C. Derivatives of the Christoffel symbols

-/

section Derivatives

variable {b : ℝ → ℝ} {r : ℝ}

lemma hasDerivAt_morrisThorneGammaR_rrr (hb : ContDiff ℝ ∞ b) (hr : r ≠ 0) (h2 : r - b r ≠ 0) :
    HasDerivAt (fun r => (r * deriv b r - b r) / (2 * r * (r - b r)))
      ((r * deriv (deriv b) r * (2 * r * (r - b r))
        - (r * deriv b r - b r) * (2 * (r - b r) + 2 * r * (1 - deriv b r)))
        / (2 * r * (r - b r)) ^ 2) r := by
  obtain ⟨hd, hd'⟩ := contDiff_infty_iff_deriv.mp hb
  have h1 : HasDerivAt b (deriv b r) r := (hd r).hasDerivAt
  have h1' : HasDerivAt (deriv b) (deriv (deriv b) r) r :=
    ((hd'.differentiable (by simp)) r).hasDerivAt
  have hN := ((hasDerivAt_id' r).mul h1').sub h1
  have hD := (((hasDerivAt_id' r).const_mul 2).mul ((hasDerivAt_id' r).sub h1))
  have := hN.fun_div hD (by simpa [mul_comm] using mul_ne_zero (mul_ne_zero two_ne_zero hr) h2)
  refine this.congr_deriv ?_
  simp only [Pi.mul_apply, Pi.sub_apply]
  ring

lemma hasDerivAt_morrisThorneGammaR_sub (hb : ContDiff ℝ ∞ b) :
    HasDerivAt (fun r => -(r - b r)) (-(1 - deriv b r)) r :=
  (((hasDerivAt_id' r).sub ((hb.differentiable (by simp)) r).hasDerivAt)).neg

lemma hasDerivAt_morrisThorneGammaR (hb : ContDiff ℝ ∞ b) (hr : r ≠ 0) (h2 : r - b r ≠ 0)
    (a i j : Fin 4) :
    HasDerivAt (morrisThorneGammaR b a i j) (morrisThorneGammaR' b a i j r) r := by
  unfold morrisThorneGammaR morrisThorneGammaR'
  split_ifs
  · exact hasDerivAt_morrisThorneGammaR_rrr hb hr h2
  · exact hasDerivAt_morrisThorneGammaR_sub hb
  · exact hasDerivAt_gammaR_inv hr
  · exact hasDerivAt_const _ _
  · exact hasDerivAt_const _ _

end Derivatives

/-!

## D. Derivatives of the metric

-/

section Entries

variable {b : ℝ → ℝ} {x : Fin 4 → ℝ} {p q : Fin 4}

lemma coordDeriv_morrisThorneMetric_tt (c : Fin 4) :
    coordDeriv (fun y => morrisThorneMetric b y 0 0) x c = 0 := by
  have : (fun y => morrisThorneMetric b y 0 0) = fun _ => -1 := by
    funext y; simp [morrisThorneMetric]
  rw [this, coordDeriv_const]

lemma coordDeriv_morrisThorneMetric_rr (hb : ContDiff ℝ ∞ b) (hx : x ∈ morrisThorneDomain b)
    (c : Fin 4) :
    coordDeriv (fun y => morrisThorneMetric b y 1 1) x c
      = if c = 1 then ((deriv b (x 1) * x 1 - b (x 1)) / x 1 ^ 2) / (1 - b (x 1) / x 1) ^ 2
        else 0 := by
  have h1 := (morrisThorneDomain.pos hx).ne'
  have h2 := (morrisThorneDomain.one_sub_pos hx).ne'
  have h5 := (morrisThorneDomain.sub_pos hx).ne'
  have hA : HasDerivAt (fun r : ℝ => (1 - b r / r)⁻¹)
      (((deriv b (x 1) * x 1 - b (x 1)) / x 1 ^ 2) / (1 - b (x 1) / x 1) ^ 2) (x 1) := by
    have hb1 : HasDerivAt b (deriv b (x 1)) (x 1) := ((hb.differentiable (by simp)) (x 1)).hasDerivAt
    have := ((hasDerivAt_const (x 1) (1 : ℝ)).sub (hb1.fun_div (hasDerivAt_id' (x 1)) h1)).inv h2
    refine this.congr_deriv ?_
    simp only [Pi.sub_apply]
    field_simp
    ring
  have : (fun y => morrisThorneMetric b y 1 1)
      = fun y => (fun r : ℝ => (1 - b r / r)⁻¹) (y 1) := by
    funext y; simp [morrisThorneMetric]
  rw [this, coordDeriv_comp_proj 1 hA.differentiableAt, hA.deriv]

lemma coordDeriv_morrisThorneMetric_θθ (c : Fin 4) :
    coordDeriv (fun y => morrisThorneMetric b y 2 2) x c = if c = 1 then 2 * x 1 else 0 := by
  have hA : HasDerivAt (fun r : ℝ => r ^ 2) (2 * x 1) (x 1) := by
    simpa using hasDerivAt_pow 2 (x 1)
  have : (fun y => morrisThorneMetric b y 2 2) = fun y => (fun r : ℝ => r ^ 2) (y 1) := by
    funext y; simp [morrisThorneMetric]
  rw [this, coordDeriv_comp_proj 1 hA.differentiableAt, hA.deriv]

lemma coordDeriv_morrisThorneMetric_φφ (c : Fin 4) :
    coordDeriv (fun y => morrisThorneMetric b y 3 3) x c
      = (if c = 1 then 2 * x 1 else 0) * sin (x 2) ^ 2
        + x 1 ^ 2 * (if c = 2 then 2 * (sin (x 2) * cos (x 2)) else 0) := by
  have hA : HasDerivAt (fun r : ℝ => r ^ 2) (2 * x 1) (x 1) := by
    simpa using hasDerivAt_pow 2 (x 1)
  have hB : HasDerivAt (fun θ : ℝ => sin θ ^ 2) (2 * (sin (x 2) * cos (x 2))) (x 2) := by
    simpa [mul_assoc] using (hasDerivAt_sin (x 2)).fun_pow 2
  have : (fun y => morrisThorneMetric b y 3 3)
      = fun y => (fun r : ℝ => r ^ 2) (y 1) * (fun θ : ℝ => sin θ ^ 2) (y 2) := by
    funext y; simp [morrisThorneMetric]
  rw [this, coordDeriv_proj_mul 1 2 hA.differentiableAt hB.differentiableAt, hA.deriv, hB.deriv]

lemma coordDeriv_morrisThorneMetric_offDiag (hpq : p ≠ q) (c : Fin 4) :
    coordDeriv (fun y => morrisThorneMetric b y p q) x c = 0 := by
  simp [morrisThorneMetric, Matrix.diagonal_apply_ne _ hpq, coordDeriv]

/-- The inverse of the Morris-Thorne metric. -/
lemma morrisThorneMetric_inv {y : Fin 4 → ℝ} (hy : y ∈ morrisThorneDomain b) :
    (morrisThorneMetric b y)⁻¹ = Matrix.diagonal
      ![-1, 1 - b (y 1) / y 1, (y 1 ^ 2)⁻¹, (y 1 ^ 2 * sin (y 2) ^ 2)⁻¹] := by
  have h1 := (morrisThorneDomain.pos hy).ne'
  have h3 := (morrisThorneDomain.sin_pos hy).ne'
  have h4 := (morrisThorneDomain.one_sub_pos hy).ne'
  have h5 := (morrisThorneDomain.sub_pos hy).ne'
  refine Matrix.inv_eq_right_inv ?_
  rw [morrisThorneMetric, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp <;> field_simp

end Entries

/-!

## E. The Christoffel symbols

-/

/-- The Christoffel symbols of the Morris-Thorne metric. -/
lemma christoffel_morrisThorne {b : ℝ → ℝ} {x : Fin 4 → ℝ} (hb : ContDiff ℝ ∞ b)
    (hx : x ∈ morrisThorneDomain b) (a i j : Fin 4) :
    christoffel (morrisThorneMetric b) x a i j
      = morrisThorneGammaR b a i j (x 1) * schwarzschildGammaTheta a i j (x 2) := by
  have h1 := (morrisThorneDomain.pos hx).ne'
  have h2 := (morrisThorneDomain.sub_pos hx).ne'
  have h3 := (morrisThorneDomain.sin_pos hx).ne'
  have h4 := (morrisThorneDomain.one_sub_pos hx).ne'
  fin_cases a <;> fin_cases i <;> fin_cases j <;>
  simp [christoffel, christoffelFirstKind, morrisThorneMetric_inv hx,
    Matrix.diagonal_apply, coordDeriv_morrisThorneMetric_tt,
    coordDeriv_morrisThorneMetric_rr hb hx,
    coordDeriv_morrisThorneMetric_θθ, coordDeriv_morrisThorneMetric_φφ,
    coordDeriv_morrisThorneMetric_offDiag, morrisThorneGammaR, schwarzschildGammaTheta]
  all_goals first | (field_simp; ring) | field_simp

end GeneralRelativity
