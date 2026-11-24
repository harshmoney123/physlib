/-
Copyright (c) 2026 Harsha Vankayalapati. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harsha Vankayalapati
-/
module

public import PhyslibAlpha.Relativity.General.MorrisThorne.RedshiftMetric

/-!

# The radial Ricci components of the Morris-Thorne wormhole with a redshift function

The components `R_tt`, `R_tr` and `R_rr` of the Ricci tensor of the Morris-Thorne metric with an
arbitrary smooth redshift function `Φ` and shape function `b`.

## i. Overview

For the metric `-e^{2Φ} dt² + (1 - b/r)⁻¹ dr² + r² dΩ²` on the region `0 < r`, `b(r) < r`, the
components of the Ricci tensor along the `t` and `r` directions are
`R_tt = e^{2Φ} ((r - b)/r (Φ'' + Φ'²) + (4 r - 3 b - r b')/(2 r²) Φ')`,
`R_tr = 0` and
`R_rr = (r b' - b)/(r² (r - b)) - (Φ'' + Φ'²) - (b - r b')/(2 r (r - b)) Φ'`
(`ricci_morrisThorneRedshift_tt`, `ricci_morrisThorneRedshift_tr`,
`ricci_morrisThorneRedshift_rr`). These are the only components needed to evaluate the Einstein
tensor on a null vector in the `t`-`r` plane. For `Φ = 0` they reduce to the components of
`morrisThorneRicci`.

The proof computes the Riemann tensor from the closed forms of the Christoffel symbols of
`PhyslibAlpha.Relativity.General.MorrisThorne.RedshiftMetric`.

## ii. Key results

- `riemann_eq_expr_of_christoffel` : the Riemann tensor of a metric whose Christoffel symbols
  factorize into an `r`-factor and a `θ`-factor, in terms of the factors.
- `ricci_morrisThorneRedshift_tt` : `R_tt`.
- `ricci_morrisThorneRedshift_tr` : `R_tr = 0`.
- `ricci_morrisThorneRedshift_rr` : `R_rr`.

## iii. Table of contents

- A. The Riemann tensor in terms of factorized Christoffel symbols
- B. The Ricci components

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

## A. The Riemann tensor in terms of factorized Christoffel symbols

-/

/-- The Riemann tensor written in terms of `r`-factors `G` (with `r`-derivatives `G'`) and the
`θ`-factors of the Schwarzschild Christoffel symbols. -/
def factorizedRiemannExpr (G G' : Fin 4 → Fin 4 → Fin 4 → ℝ → ℝ) (x : Fin 4 → ℝ)
    (a i c d : Fin 4) : ℝ :=
  ((if c = 1 then G' a d i (x 1) else 0) * schwarzschildGammaTheta a d i (x 2)
    + G a d i (x 1) * (if c = 2 then schwarzschildGammaTheta' a d i (x 2) else 0))
  - ((if d = 1 then G' a c i (x 1) else 0) * schwarzschildGammaTheta a c i (x 2)
    + G a c i (x 1) * (if d = 2 then schwarzschildGammaTheta' a c i (x 2) else 0))
  + ∑ e, (G a c e (x 1) * schwarzschildGammaTheta a c e (x 2)
        * (G e d i (x 1) * schwarzschildGammaTheta e d i (x 2))
      - G a d e (x 1) * schwarzschildGammaTheta a d e (x 2)
        * (G e c i (x 1) * schwarzschildGammaTheta e c i (x 2)))

/-- If the Christoffel symbols of `g` near `x` are `G a i j (r) * schwarzschildGammaTheta a i j (θ)`
with differentiable `G`, then the Riemann tensor of `g` at `x` is `factorizedRiemannExpr G G' x`. -/
lemma riemann_eq_expr_of_christoffel {g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
    {G G' : Fin 4 → Fin 4 → Fin 4 → ℝ → ℝ} {x : Fin 4 → ℝ} (h3 : sin (x 2) ≠ 0)
    (hcongr : ∀ a i j : Fin 4, (fun y => christoffel g y a i j)
      =ᶠ[nhds x] fun y => G a i j (y 1) * schwarzschildGammaTheta a i j (y 2))
    (hR : ∀ a i j, HasDerivAt (G a i j) (G' a i j (x 1)) (x 1)) (a i c d : Fin 4) :
    riemann g x a i c d = factorizedRiemannExpr G G' x a i c d := by
  have hT : ∀ a i j, HasDerivAt (schwarzschildGammaTheta a i j)
      (schwarzschildGammaTheta' a i j (x 2)) (x 2) := hasDerivAt_gammaTheta h3
  have hD : ∀ a i j e, coordDeriv (fun y => christoffel g y a i j) x e
      = (if e = 1 then G' a i j (x 1) else 0) * schwarzschildGammaTheta a i j (x 2)
        + G a i j (x 1) * (if e = 2 then schwarzschildGammaTheta' a i j (x 2) else 0) :=
    fun a i j e => by
    rw [coordDeriv_congr (hcongr a i j) e, coordDeriv_proj_mul 1 2 (hR a i j).differentiableAt
      (hT a i j).differentiableAt, (hR a i j).deriv, (hT a i j).deriv]
  have hx : ∀ a i j, christoffel g x a i j
      = G a i j (x 1) * schwarzschildGammaTheta a i j (x 2) := fun a i j =>
    (hcongr a i j).eq_of_nhds
  unfold riemann factorizedRiemannExpr
  rw [hD, hD]
  simp only [hx]

/-!

## B. The Ricci components

-/

section Ricci

variable {Φ b : ℝ → ℝ} {x : Fin 4 → ℝ}

/-- The Riemann tensor of the Morris-Thorne metric with a redshift function. -/
lemma riemann_morrisThorneRedshift_expr (hΦ : ContDiff ℝ ∞ Φ) (hb : ContDiff ℝ ∞ b)
    (hx : x ∈ morrisThorneDomain b) (a i c d : Fin 4) :
    riemann (morrisThorneRedshiftMetric Φ b) x a i c d
      = factorizedRiemannExpr (morrisThorneRedshiftGammaR Φ b) (morrisThorneRedshiftGammaR' Φ b)
        x a i c d :=
  riemann_eq_expr_of_christoffel (morrisThorneDomain.sin_pos hx).ne'
    (fun a i j => by
      filter_upwards [(isOpen_morrisThorneDomain hb.continuous).mem_nhds hx] with y hy
      exact christoffel_morrisThorneRedshift hΦ hb hy a i j)
    (fun a i j => hasDerivAt_morrisThorneRedshiftGammaR hΦ hb (morrisThorneDomain.pos hx).ne'
      (morrisThorneDomain.sub_pos hx).ne' a i j) a i c d

/-- The component `R_tt` of the Ricci tensor of the Morris-Thorne metric with a redshift function:
`e^{2Φ} ((r - b)/r (Φ'' + Φ'²) + (4 r - 3 b - r b')/(2 r²) Φ')`. -/
lemma ricci_morrisThorneRedshift_tt (hΦ : ContDiff ℝ ∞ Φ) (hb : ContDiff ℝ ∞ b)
    (hx : x ∈ morrisThorneDomain b) :
    ricci (morrisThorneRedshiftMetric Φ b) x 0 0
      = exp (2 * Φ (x 1)) * ((x 1 - b (x 1)) / x 1
          * (deriv (deriv Φ) (x 1) + deriv Φ (x 1) ^ 2)
        + (4 * x 1 - 3 * b (x 1) - x 1 * deriv b (x 1)) / (2 * x 1 ^ 2) * deriv Φ (x 1)) := by
  have h1 := (morrisThorneDomain.pos hx).ne'
  have h2 := (morrisThorneDomain.sub_pos hx).ne'
  simp only [ricci, riemann_morrisThorneRedshift_expr hΦ hb hx]
  simp [Fin.sum_univ_four, factorizedRiemannExpr, morrisThorneRedshiftGammaR,
    morrisThorneRedshiftGammaR', morrisThorneGammaR, morrisThorneGammaR',
    schwarzschildGammaTheta, schwarzschildGammaTheta']
  field_simp
  ring

/-- The component `R_tr` of the Ricci tensor of the Morris-Thorne metric with a redshift function
vanishes. -/
lemma ricci_morrisThorneRedshift_tr (hΦ : ContDiff ℝ ∞ Φ) (hb : ContDiff ℝ ∞ b)
    (hx : x ∈ morrisThorneDomain b) :
    ricci (morrisThorneRedshiftMetric Φ b) x 0 1 = 0 := by
  have h1 := (morrisThorneDomain.pos hx).ne'
  have h2 := (morrisThorneDomain.sub_pos hx).ne'
  simp only [ricci, riemann_morrisThorneRedshift_expr hΦ hb hx]
  simp [Fin.sum_univ_four, factorizedRiemannExpr, morrisThorneRedshiftGammaR,
    morrisThorneRedshiftGammaR', morrisThorneGammaR, morrisThorneGammaR',
    schwarzschildGammaTheta, schwarzschildGammaTheta']

/-- The component `R_rr` of the Ricci tensor of the Morris-Thorne metric with a redshift function:
`(r b' - b)/(r² (r - b)) - (Φ'' + Φ'²) - (b - r b')/(2 r (r - b)) Φ'`. -/
lemma ricci_morrisThorneRedshift_rr (hΦ : ContDiff ℝ ∞ Φ) (hb : ContDiff ℝ ∞ b)
    (hx : x ∈ morrisThorneDomain b) :
    ricci (morrisThorneRedshiftMetric Φ b) x 1 1
      = (x 1 * deriv b (x 1) - b (x 1)) / (x 1 ^ 2 * (x 1 - b (x 1)))
        - (deriv (deriv Φ) (x 1) + deriv Φ (x 1) ^ 2)
        - (b (x 1) - x 1 * deriv b (x 1)) / (2 * x 1 * (x 1 - b (x 1))) * deriv Φ (x 1) := by
  have h1 := (morrisThorneDomain.pos hx).ne'
  have h2 := (morrisThorneDomain.sub_pos hx).ne'
  simp only [ricci, riemann_morrisThorneRedshift_expr hΦ hb hx]
  simp [Fin.sum_univ_four, factorizedRiemannExpr, morrisThorneRedshiftGammaR,
    morrisThorneRedshiftGammaR', morrisThorneGammaR, morrisThorneGammaR',
    schwarzschildGammaTheta, schwarzschildGammaTheta']
  field_simp
  ring

end Ricci

end GeneralRelativity
