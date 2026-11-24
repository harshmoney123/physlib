/-
Copyright (c) 2026 Harsha Vankayalapati. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harsha Vankayalapati
-/
module

public import PhyslibAlpha.Relativity.General.Schwarzschild.Metric

/-!

# The Schwarzschild metric is a vacuum solution

The Riemann tensor of the Schwarzschild metric, its vanishing Ricci tensor and its Kretschmann
scalar `48 M² / r⁶`.

## i. Overview

On the exterior region `r > 2M` (with `M > 0`) the Riemann tensor `R^a_{bcd}` of the Schwarzschild
metric in Schwarzschild coordinates is, for `a ≠ b`,
`R^a_{bcd} = g_{bb} K_{ab} (δ^a_c δ^b_d - δ^a_d δ^b_c)`, with `K_{tr} = K_{θφ} = 2M/r³` and
`K_{ab} = -M/r³` for the other pairs, and it vanishes for `a = b` (`riemann_schwarzschild`).
The proof computes the Riemann tensor from the closed forms of the Christoffel symbols of
`PhyslibAlpha.Relativity.General.Schwarzschild.Metric`, one component at a time.

From this we obtain that the Ricci tensor vanishes (`ricci_schwarzschild`), hence so do the Ricci
scalar and the Einstein tensor, and that the Kretschmann scalar `R_{abcd} R^{abcd}` equals
`48 M² / r⁶` (`kretschmann_schwarzschild`), which is finite for `r > 0`: the singularity at `r = 0`
is a curvature singularity.

## ii. Key results

- `schwarzschildRiemann` : the Riemann tensor of the Schwarzschild metric in closed form.
- `riemann_schwarzschild` : the Riemann tensor of `schwarzschildMetric` is `schwarzschildRiemann`.
- `ricci_schwarzschild` : the Ricci tensor vanishes, so Schwarzschild is a vacuum solution.
- `ricciScalar_schwarzschild`, `einstein_schwarzschild` : the Ricci scalar and the Einstein tensor
  vanish.
- `kretschmann_schwarzschild` : the Kretschmann scalar is `48 M² / r⁶`.

## iii. Table of contents

- A. The Riemann tensor in closed form
- B. Computing the Riemann tensor
- C. Vacuum
- D. The Kretschmann scalar

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

## A. The Riemann tensor in closed form

-/

/-- The curvature `R^{ab}{}_{ab}` of the `(a, b)` coordinate plane of the Schwarzschild metric. -/
def schwarzschildCurvature (M : ℝ) (a b : Fin 4) (r : ℝ) : ℝ :=
  if (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) ∨ (a = 2 ∧ b = 3) ∨ (a = 3 ∧ b = 2) then 2 * M / r ^ 3
  else -(M / r ^ 3)

/-- The Riemann tensor `R^a_{bcd}` of the Schwarzschild metric. -/
def schwarzschildRiemann (M : ℝ) (x : Fin 4 → ℝ) (a b c d : Fin 4) : ℝ :=
  if a = b then 0
  else schwarzschildMetric M x b b * schwarzschildCurvature M a b (x 1)
    * ((if a = c ∧ b = d then 1 else 0) - (if a = d ∧ b = c then 1 else 0))

/-!

## B. Computing the Riemann tensor

-/

/-- The Riemann tensor of the Schwarzschild metric written with the closed forms of the Christoffel
symbols and their derivatives. -/
def schwarzschildRiemannExpr (M : ℝ) (x : Fin 4 → ℝ) (a b c d : Fin 4) : ℝ :=
  ((if c = 1 then schwarzschildGammaR' M a d b (x 1) else 0)
      * schwarzschildGammaTheta a d b (x 2)
    + schwarzschildGammaR M a d b (x 1)
      * (if c = 2 then schwarzschildGammaTheta' a d b (x 2) else 0))
  - ((if d = 1 then schwarzschildGammaR' M a c b (x 1) else 0)
      * schwarzschildGammaTheta a c b (x 2)
    + schwarzschildGammaR M a c b (x 1)
      * (if d = 2 then schwarzschildGammaTheta' a c b (x 2) else 0))
  + ∑ e, (schwarzschildGammaR M a c e (x 1) * schwarzschildGammaTheta a c e (x 2)
        * (schwarzschildGammaR M e d b (x 1) * schwarzschildGammaTheta e d b (x 2))
      - schwarzschildGammaR M a d e (x 1) * schwarzschildGammaTheta a d e (x 2)
        * (schwarzschildGammaR M e c b (x 1) * schwarzschildGammaTheta e c b (x 2)))

/-- The Riemann tensor of the Schwarzschild metric in terms of the closed forms. -/
lemma riemann_schwarzschild_expr {M : ℝ} {x : Fin 4 → ℝ} (hM : 0 < M)
    (hx : x ∈ schwarzschildDomain M) (a b c d : Fin 4) :
    riemann (schwarzschildMetric M) x a b c d = schwarzschildRiemannExpr M x a b c d := by
  have h1 := (schwarzschildDomain.pos hM hx).ne'
  have h2 := (schwarzschildDomain.sub_pos hx).ne'
  have h3 := (schwarzschildDomain.sin_pos hx).ne'
  have hcongr : ∀ a b c : Fin 4, (fun y => christoffel (schwarzschildMetric M) y a b c)
      =ᶠ[nhds x] fun y => schwarzschildGammaR M a b c (y 1) * schwarzschildGammaTheta a b c (y 2) :=
    fun a b c => by
      filter_upwards [(isOpen_schwarzschildDomain M).mem_nhds hx] with y hy
      exact christoffel_schwarzschild hM hy a b c
  have hR : ∀ a b c, HasDerivAt (schwarzschildGammaR M a b c)
      (schwarzschildGammaR' M a b c (x 1)) (x 1) := hasDerivAt_gammaR h1 h2
  have hT : ∀ a b c, HasDerivAt (schwarzschildGammaTheta a b c)
      (schwarzschildGammaTheta' a b c (x 2)) (x 2) := hasDerivAt_gammaTheta h3
  have hD : ∀ a b c e, coordDeriv (fun y => christoffel (schwarzschildMetric M) y a b c) x e
      = (if e = 1 then schwarzschildGammaR' M a b c (x 1) else 0)
          * schwarzschildGammaTheta a b c (x 2)
        + schwarzschildGammaR M a b c (x 1)
          * (if e = 2 then schwarzschildGammaTheta' a b c (x 2) else 0) := fun a b c e => by
    rw [coordDeriv_congr (hcongr a b c) e, coordDeriv_proj_mul 1 2 (hR a b c).differentiableAt
      (hT a b c).differentiableAt, (hR a b c).deriv, (hT a b c).deriv]
  unfold riemann schwarzschildRiemannExpr
  rw [hD, hD]
  simp only [christoffel_schwarzschild hM hx]

/-- The component `a = 0` of `riemann_schwarzschild_expr` agrees with the closed form. -/
lemma schwarzschildRiemannExpr_zero {M : ℝ} {x : Fin 4 → ℝ} (hM : 0 < M)
    (hx : x ∈ schwarzschildDomain M) (b c d : Fin 4) :
    schwarzschildRiemannExpr M x 0 b c d = schwarzschildRiemann M x 0 b c d := by
  have h1 := (schwarzschildDomain.pos hM hx).ne'
  have h2 := (schwarzschildDomain.sub_pos hx).ne'
  have h2' : x 1 - M * 2 ≠ 0 := by rw [mul_comm]; exact h2
  have h3 := (schwarzschildDomain.sin_pos hx).ne'
  have h4 := (schwarzschildDomain.one_sub_pos hM hx).ne'
  fin_cases b <;> fin_cases c <;> fin_cases d <;>
  simp [Fin.sum_univ_four, schwarzschildRiemannExpr, schwarzschildGammaR, schwarzschildGammaR',
    schwarzschildGammaTheta, schwarzschildGammaTheta', schwarzschildRiemann,
    schwarzschildCurvature, schwarzschildMetric]
  all_goals (field_simp; ring1)

/-- The component `a = 1` of `riemann_schwarzschild_expr` agrees with the closed form. -/
lemma schwarzschildRiemannExpr_one {M : ℝ} {x : Fin 4 → ℝ} (hM : 0 < M)
    (hx : x ∈ schwarzschildDomain M) (b c d : Fin 4) :
    schwarzschildRiemannExpr M x 1 b c d = schwarzschildRiemann M x 1 b c d := by
  have h1 := (schwarzschildDomain.pos hM hx).ne'
  have h2 := (schwarzschildDomain.sub_pos hx).ne'
  have h2' : x 1 - M * 2 ≠ 0 := by rw [mul_comm]; exact h2
  have h3 := (schwarzschildDomain.sin_pos hx).ne'
  have h4 := (schwarzschildDomain.one_sub_pos hM hx).ne'
  fin_cases b <;> fin_cases c <;> fin_cases d <;>
  simp [Fin.sum_univ_four, schwarzschildRiemannExpr, schwarzschildGammaR, schwarzschildGammaR',
    schwarzschildGammaTheta, schwarzschildGammaTheta', schwarzschildRiemann,
    schwarzschildCurvature, schwarzschildMetric]
  all_goals (field_simp; ring1)

/-- The component `a = 2` of `riemann_schwarzschild_expr` agrees with the closed form. -/
lemma schwarzschildRiemannExpr_two {M : ℝ} {x : Fin 4 → ℝ} (hM : 0 < M)
    (hx : x ∈ schwarzschildDomain M) (b c d : Fin 4) :
    schwarzschildRiemannExpr M x 2 b c d = schwarzschildRiemann M x 2 b c d := by
  have h1 := (schwarzschildDomain.pos hM hx).ne'
  have h2 := (schwarzschildDomain.sub_pos hx).ne'
  have h2' : x 1 - M * 2 ≠ 0 := by rw [mul_comm]; exact h2
  have h3 := (schwarzschildDomain.sin_pos hx).ne'
  have h4 := (schwarzschildDomain.one_sub_pos hM hx).ne'
  fin_cases b <;> fin_cases c <;> fin_cases d <;>
  simp [Fin.sum_univ_four, schwarzschildRiemannExpr, schwarzschildGammaR, schwarzschildGammaR',
    schwarzschildGammaTheta, schwarzschildGammaTheta', schwarzschildRiemann,
    schwarzschildCurvature, schwarzschildMetric]
  all_goals (field_simp; ring1)

/-- The component `a = 3` of `riemann_schwarzschild_expr` agrees with the closed form. -/
lemma schwarzschildRiemannExpr_three {M : ℝ} {x : Fin 4 → ℝ} (hM : 0 < M)
    (hx : x ∈ schwarzschildDomain M) (b c d : Fin 4) :
    schwarzschildRiemannExpr M x 3 b c d = schwarzschildRiemann M x 3 b c d := by
  have h1 := (schwarzschildDomain.pos hM hx).ne'
  have h2 := (schwarzschildDomain.sub_pos hx).ne'
  have h2' : x 1 - M * 2 ≠ 0 := by rw [mul_comm]; exact h2
  have h3 := (schwarzschildDomain.sin_pos hx).ne'
  have h4 := (schwarzschildDomain.one_sub_pos hM hx).ne'
  fin_cases b <;> fin_cases c <;> fin_cases d <;>
  simp [Fin.sum_univ_four, schwarzschildRiemannExpr, schwarzschildGammaR, schwarzschildGammaR',
    schwarzschildGammaTheta, schwarzschildGammaTheta', schwarzschildRiemann,
    schwarzschildCurvature, schwarzschildMetric]
  all_goals first | (field_simp; ring1) | (field_simp; simp only [cos_sq']; ring1)

/-- The Riemann tensor of the Schwarzschild metric on the exterior region. -/
lemma riemann_schwarzschild {M : ℝ} {x : Fin 4 → ℝ} (hM : 0 < M) (hx : x ∈ schwarzschildDomain M)
    (a b c d : Fin 4) :
    riemann (schwarzschildMetric M) x a b c d = schwarzschildRiemann M x a b c d := by
  rw [riemann_schwarzschild_expr hM hx]
  fin_cases a
  exacts [schwarzschildRiemannExpr_zero hM hx b c d, schwarzschildRiemannExpr_one hM hx b c d,
    schwarzschildRiemannExpr_two hM hx b c d, schwarzschildRiemannExpr_three hM hx b c d]

/-!

## C. Vacuum

-/

/-- The Schwarzschild metric is a vacuum solution: its Ricci tensor vanishes. -/
theorem ricci_schwarzschild {M : ℝ} {x : Fin 4 → ℝ} (hM : 0 < M) (hx : x ∈ schwarzschildDomain M)
    (b d : Fin 4) : ricci (schwarzschildMetric M) x b d = 0 := by
  simp only [ricci, riemann_schwarzschild hM hx]
  fin_cases b <;> fin_cases d <;>
  simp [Fin.sum_univ_four, schwarzschildRiemann, schwarzschildCurvature]
  all_goals ring

/-- The Ricci scalar of the Schwarzschild metric vanishes. -/
lemma ricciScalar_schwarzschild {M : ℝ} {x : Fin 4 → ℝ} (hM : 0 < M)
    (hx : x ∈ schwarzschildDomain M) : ricciScalar (schwarzschildMetric M) x = 0 := by
  simp [ricciScalar, ricci_schwarzschild hM hx]

/-- The Einstein tensor of the Schwarzschild metric vanishes. -/
lemma einstein_schwarzschild {M : ℝ} {x : Fin 4 → ℝ} (hM : 0 < M)
    (hx : x ∈ schwarzschildDomain M) (a b : Fin 4) :
    einstein (schwarzschildMetric M) x a b = 0 := by
  simp [einstein, ricci_schwarzschild hM hx, ricciScalar_schwarzschild hM hx]

/-!

## D. The Kretschmann scalar

-/

/-- The Kretschmann scalar of the Schwarzschild metric is `48 M² / r⁶`. -/
theorem kretschmann_schwarzschild {M : ℝ} {x : Fin 4 → ℝ} (hM : 0 < M)
    (hx : x ∈ schwarzschildDomain M) :
    kretschmann (schwarzschildMetric M) x = 48 * M ^ 2 / x 1 ^ 6 := by
  have h1 := (schwarzschildDomain.pos hM hx).ne'
  have h2 := (schwarzschildDomain.sub_pos hx).ne'
  have h2' : x 1 - M * 2 ≠ 0 := by rw [mul_comm]; exact h2
  have h3 := (schwarzschildDomain.sin_pos hx).ne'
  have h4 := (schwarzschildDomain.one_sub_pos hM hx).ne'
  rw [kretschmann_diagonal (g := schwarzschildMetric M) rfl (schwarzschildMetric_inv hM hx)]
  simp only [riemann_schwarzschild hM hx]
  simp [Fin.sum_univ_four, schwarzschildRiemann, schwarzschildCurvature, schwarzschildMetric]
  field_simp
  ring

end GeneralRelativity
