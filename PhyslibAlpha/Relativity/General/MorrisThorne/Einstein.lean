/-
Copyright (c) 2026 Harsha Vankayalapati. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harsha Vankayalapati
-/
module

public import PhyslibAlpha.Relativity.General.MorrisThorne.Metric

/-!

# The Ricci and Einstein tensors of the Morris-Thorne wormhole

The Ricci tensor, the Ricci scalar and the Einstein tensor of the Morris-Thorne metric with zero
redshift function and arbitrary shape function `b`.

## i. Overview

For the metric `-dt² + (1 - b(r)/r)⁻¹ dr² + r² dθ² + r² sin²θ dφ²` on the region `0 < r`,
`b(r) < r`, the Ricci tensor is diagonal (`ricci_morrisThorne`) with
`R_tt = 0`, `R_rr = (r b' - b) / (r² (r - b))`, `R_θθ = (b + r b') / (2 r)` and
`R_φφ = sin²θ R_θθ`. The Ricci scalar is `R = 2 b' / r²` (`ricciScalar_morrisThorne`), and the
Einstein tensor is diagonal (`einstein_morrisThorne`) with
`G_tt = b' / r²`, `G_rr = -b / (r² (r - b))`, `G_θθ = (b - r b') / (2 r)` and
`G_φφ = sin²θ G_θθ`.
The proof computes the Ricci tensor from the closed forms of the Christoffel symbols of
`PhyslibAlpha.Relativity.General.MorrisThorne.Metric`, one component at a time.

## ii. Key results

- `morrisThorneRicci` : the Ricci tensor of the Morris-Thorne metric in closed form.
- `ricci_morrisThorne` : the Ricci tensor of `morrisThorneMetric` is `morrisThorneRicci`.
- `ricciScalar_morrisThorne` : the Ricci scalar is `2 b' / r²`.
- `morrisThorneEinstein`, `einstein_morrisThorne` : the Einstein tensor in closed form.

## iii. Table of contents

- A. The Riemann tensor in terms of the closed forms
- B. The Ricci tensor
- C. The Ricci scalar and the Einstein tensor

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

## A. The Riemann tensor in terms of the closed forms

-/

/-- The Riemann tensor of the Morris-Thorne metric written with the closed forms of the
Christoffel symbols and their derivatives. -/
def morrisThorneRiemannExpr (b : ℝ → ℝ) (x : Fin 4 → ℝ) (a i c d : Fin 4) : ℝ :=
  ((if c = 1 then morrisThorneGammaR' b a d i (x 1) else 0)
      * schwarzschildGammaTheta a d i (x 2)
    + morrisThorneGammaR b a d i (x 1)
      * (if c = 2 then schwarzschildGammaTheta' a d i (x 2) else 0))
  - ((if d = 1 then morrisThorneGammaR' b a c i (x 1) else 0)
      * schwarzschildGammaTheta a c i (x 2)
    + morrisThorneGammaR b a c i (x 1)
      * (if d = 2 then schwarzschildGammaTheta' a c i (x 2) else 0))
  + ∑ e, (morrisThorneGammaR b a c e (x 1) * schwarzschildGammaTheta a c e (x 2)
        * (morrisThorneGammaR b e d i (x 1) * schwarzschildGammaTheta e d i (x 2))
      - morrisThorneGammaR b a d e (x 1) * schwarzschildGammaTheta a d e (x 2)
        * (morrisThorneGammaR b e c i (x 1) * schwarzschildGammaTheta e c i (x 2)))

/-- The Riemann tensor of the Morris-Thorne metric in terms of the closed forms. -/
lemma riemann_morrisThorne_expr {b : ℝ → ℝ} {x : Fin 4 → ℝ} (hb : ContDiff ℝ ∞ b)
    (hx : x ∈ morrisThorneDomain b) (a i c d : Fin 4) :
    riemann (morrisThorneMetric b) x a i c d = morrisThorneRiemannExpr b x a i c d := by
  have h1 := (morrisThorneDomain.pos hx).ne'
  have h2 := (morrisThorneDomain.sub_pos hx).ne'
  have h3 := (morrisThorneDomain.sin_pos hx).ne'
  have hcongr : ∀ a i j : Fin 4, (fun y => christoffel (morrisThorneMetric b) y a i j)
      =ᶠ[nhds x] fun y => morrisThorneGammaR b a i j (y 1) * schwarzschildGammaTheta a i j (y 2) :=
    fun a i j => by
      filter_upwards [(isOpen_morrisThorneDomain hb.continuous).mem_nhds hx] with y hy
      exact christoffel_morrisThorne hb hy a i j
  have hR : ∀ a i j, HasDerivAt (morrisThorneGammaR b a i j)
      (morrisThorneGammaR' b a i j (x 1)) (x 1) := hasDerivAt_morrisThorneGammaR hb h1 h2
  have hT : ∀ a i j, HasDerivAt (schwarzschildGammaTheta a i j)
      (schwarzschildGammaTheta' a i j (x 2)) (x 2) := hasDerivAt_gammaTheta h3
  have hD : ∀ a i j e, coordDeriv (fun y => christoffel (morrisThorneMetric b) y a i j) x e
      = (if e = 1 then morrisThorneGammaR' b a i j (x 1) else 0)
          * schwarzschildGammaTheta a i j (x 2)
        + morrisThorneGammaR b a i j (x 1)
          * (if e = 2 then schwarzschildGammaTheta' a i j (x 2) else 0) := fun a i j e => by
    rw [coordDeriv_congr (hcongr a i j) e, coordDeriv_proj_mul 1 2 (hR a i j).differentiableAt
      (hT a i j).differentiableAt, (hR a i j).deriv, (hT a i j).deriv]
  unfold riemann morrisThorneRiemannExpr
  rw [hD, hD]
  simp only [christoffel_morrisThorne hb hx]

/-!

## B. The Ricci tensor

-/

/-- The Ricci tensor of the Morris-Thorne metric: it is diagonal, with
`R_tt = 0`, `R_rr = (r b' - b) / (r² (r - b))`, `R_θθ = (b + r b') / (2 r)` and
`R_φφ = sin²θ R_θθ`. -/
def morrisThorneRicci (b : ℝ → ℝ) (x : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.diagonal ![0, (x 1 * deriv b (x 1) - b (x 1)) / (x 1 ^ 2 * (x 1 - b (x 1))),
    (b (x 1) + x 1 * deriv b (x 1)) / (2 * x 1),
    sin (x 2) ^ 2 * ((b (x 1) + x 1 * deriv b (x 1)) / (2 * x 1))]

/-- The Ricci tensor of the Morris-Thorne metric. -/
lemma ricci_morrisThorne {b : ℝ → ℝ} {x : Fin 4 → ℝ} (hb : ContDiff ℝ ∞ b)
    (hx : x ∈ morrisThorneDomain b) (i d : Fin 4) :
    ricci (morrisThorneMetric b) x i d = morrisThorneRicci b x i d := by
  have h1 := (morrisThorneDomain.pos hx).ne'
  have h2 := (morrisThorneDomain.sub_pos hx).ne'
  have h3 := (morrisThorneDomain.sin_pos hx).ne'
  have h2' : x 1 - b (x 1) ≠ 0 := h2
  simp only [ricci, riemann_morrisThorne_expr hb hx]
  fin_cases i <;> fin_cases d <;>
  simp [Fin.sum_univ_four, morrisThorneRiemannExpr, morrisThorneGammaR, morrisThorneGammaR',
    schwarzschildGammaTheta, schwarzschildGammaTheta', morrisThorneRicci]
  all_goals first | (field_simp; ring1) | (field_simp; simp only [cos_sq']; ring1)

/-!

## C. The Ricci scalar and the Einstein tensor

-/

/-- The Ricci scalar of the Morris-Thorne metric is `2 b' / r²`. -/
lemma ricciScalar_morrisThorne {b : ℝ → ℝ} {x : Fin 4 → ℝ} (hb : ContDiff ℝ ∞ b)
    (hx : x ∈ morrisThorneDomain b) :
    ricciScalar (morrisThorneMetric b) x = 2 * deriv b (x 1) / x 1 ^ 2 := by
  have h1 := (morrisThorneDomain.pos hx).ne'
  have h2 := (morrisThorneDomain.sub_pos hx).ne'
  have h3 := (morrisThorneDomain.sin_pos hx).ne'
  simp only [ricciScalar, morrisThorneMetric_inv hx, ricci_morrisThorne hb hx]
  simp [Fin.sum_univ_four, morrisThorneRicci, Matrix.diagonal_apply]
  field_simp
  ring

/-- The Einstein tensor of the Morris-Thorne metric: it is diagonal, with `G_tt = b' / r²`,
`G_rr = -b / (r² (r - b))`, `G_θθ = (b - r b') / (2 r)` and `G_φφ = sin²θ G_θθ`. -/
def morrisThorneEinstein (b : ℝ → ℝ) (x : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.diagonal ![deriv b (x 1) / x 1 ^ 2, -b (x 1) / (x 1 ^ 2 * (x 1 - b (x 1))),
    (b (x 1) - x 1 * deriv b (x 1)) / (2 * x 1),
    sin (x 2) ^ 2 * ((b (x 1) - x 1 * deriv b (x 1)) / (2 * x 1))]

/-- The Einstein tensor of the Morris-Thorne metric. -/
lemma einstein_morrisThorne {b : ℝ → ℝ} {x : Fin 4 → ℝ} (hb : ContDiff ℝ ∞ b)
    (hx : x ∈ morrisThorneDomain b) (i j : Fin 4) :
    einstein (morrisThorneMetric b) x i j = morrisThorneEinstein b x i j := by
  have h1 := (morrisThorneDomain.pos hx).ne'
  have h2 := (morrisThorneDomain.sub_pos hx).ne'
  have h4 := (morrisThorneDomain.one_sub_pos hx).ne'
  have h2' : x 1 - b (x 1) ≠ 0 := h2
  simp only [einstein, ricci_morrisThorne hb hx, ricciScalar_morrisThorne hb hx]
  fin_cases i <;> fin_cases j <;>
  simp [morrisThorneMetric, morrisThorneRicci, morrisThorneEinstein]
  all_goals first | ring1 | (field_simp; ring1)

end GeneralRelativity
