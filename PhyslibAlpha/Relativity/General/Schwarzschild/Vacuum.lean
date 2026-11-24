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
scalar `48 G² M² / (c⁴ r⁶)`.

## i. Overview

Here `G : ℝ` is Newton's constant, `c : SpeedOfLight` is the speed of light (take `c = 1` for
units in which it is one), `M : ℝ` is the mass and `r_s = 2GM/c²` is the Schwarzschild radius
(`schwarzschildRadius`). On the exterior region `r > r_s` (with `G > 0` and `M > 0`) the Riemann
tensor `R^a_{bcd}` of the Schwarzschild metric in Schwarzschild coordinates and the signature
`(+,-,-,-)` is, for `a ≠ b`,
`R^a_{bcd} = g_{bb} K_{ab} (δ^a_c δ^b_d - δ^a_d δ^b_c)`, with `K_{tr} = K_{θφ} = -r_s/r³` and
`K_{ab} = r_s/(2r³)` for the other pairs, and it vanishes for `a = b` (`riemann_schwarzschild`).
The proof computes the Riemann tensor from the closed forms of the Christoffel symbols of
`PhyslibAlpha.Relativity.General.Schwarzschild.Metric`, one component at a time.

From this we obtain that the Ricci tensor vanishes (`ricci_schwarzschild`), hence so do the Ricci
scalar and the Einstein tensor, and that the Kretschmann scalar `R_{abcd} R^{abcd}` equals
`48 G² M² / (c⁴ r⁶) = 12 r_s² / r⁶` (`kretschmann_schwarzschild`), which is finite for `r > 0`:
the singularity at `r = 0` is a curvature singularity.

## ii. Key results

- `schwarzschildRiemann` : the Riemann tensor of the Schwarzschild metric in closed form.
- `riemann_schwarzschild` : the Riemann tensor of `schwarzschildMetric` is `schwarzschildRiemann`.
- `ricci_schwarzschild` : the Ricci tensor vanishes, so Schwarzschild is a vacuum solution.
- `ricciScalar_schwarzschild`, `einstein_schwarzschild` : the Ricci scalar and the Einstein tensor
  vanish.
- `kretschmann_schwarzschild` : the Kretschmann scalar is `48 G² M² / (c⁴ r⁶)`.

## iii. Table of contents

- A. The Riemann tensor in closed form
- B. Computing the Riemann tensor
- C. Vacuum
- D. The Kretschmann scalar

## iv. References

- K. Schwarzschild, *Über das Gravitationsfeld eines Massenpunktes nach der Einsteinschen
  Theorie*, Sitzungsber. Preuss. Akad. Wiss. (1916).
- R. M. Wald, *General Relativity*, Chapter 6 (in the opposite sign convention `(-,+,+,+)` and
  units with `G = c = 1`).

-/

@[expose] public section

noncomputable section

namespace GeneralRelativity

open Real

/-!

## A. The Riemann tensor in closed form

-/

/-- The curvature `R^{ai}{}_{ai}` of the `(a, i)` coordinate plane of the Schwarzschild metric in
the signature `(+,-,-,-)`: `-r_s/r³` for the `(t, r)` and `(θ, φ)` planes and `r_s/(2r³)` for the
others, with `r_s = 2GM/c²`. -/
def schwarzschildCurvature (G : ℝ) (c : SpeedOfLight) (M : ℝ) (a i : Fin 4) (r : ℝ) : ℝ :=
  if (a = 0 ∧ i = 1) ∨ (a = 1 ∧ i = 0) ∨ (a = 2 ∧ i = 3) ∨ (a = 3 ∧ i = 2) then
    -(schwarzschildRadius G c M / r ^ 3)
  else schwarzschildRadius G c M / (2 * r ^ 3)

/-- The Riemann tensor `R^a_{ijk}` of the Schwarzschild metric. -/
def schwarzschildRiemann (G : ℝ) (c : SpeedOfLight) (M : ℝ) (x : Fin 4 → ℝ) (a i j k : Fin 4) :
    ℝ :=
  if a = i then 0
  else schwarzschildMetric G c M x i i * schwarzschildCurvature G c M a i (x 1)
    * ((if a = j ∧ i = k then 1 else 0) - (if a = k ∧ i = j then 1 else 0))

/-!

## B. Computing the Riemann tensor

-/

/-- The Riemann tensor of the Schwarzschild metric written with the closed forms of the Christoffel
symbols and their derivatives. -/
def schwarzschildRiemannExpr (G : ℝ) (c : SpeedOfLight) (M : ℝ) (x : Fin 4 → ℝ)
    (a i j k : Fin 4) : ℝ :=
  ((if j = 1 then schwarzschildGammaR' G c M a k i (x 1) else 0)
      * schwarzschildGammaTheta a k i (x 2)
    + schwarzschildGammaR G c M a k i (x 1)
      * (if j = 2 then schwarzschildGammaTheta' a k i (x 2) else 0))
  - ((if k = 1 then schwarzschildGammaR' G c M a j i (x 1) else 0)
      * schwarzschildGammaTheta a j i (x 2)
    + schwarzschildGammaR G c M a j i (x 1)
      * (if k = 2 then schwarzschildGammaTheta' a j i (x 2) else 0))
  + ∑ e, (schwarzschildGammaR G c M a j e (x 1) * schwarzschildGammaTheta a j e (x 2)
        * (schwarzschildGammaR G c M e k i (x 1) * schwarzschildGammaTheta e k i (x 2))
      - schwarzschildGammaR G c M a k e (x 1) * schwarzschildGammaTheta a k e (x 2)
        * (schwarzschildGammaR G c M e j i (x 1) * schwarzschildGammaTheta e j i (x 2)))

/-- The Riemann tensor of the Schwarzschild metric in terms of the closed forms. -/
lemma riemann_schwarzschild_expr {G : ℝ} {c : SpeedOfLight} {M : ℝ} {x : Fin 4 → ℝ} (hG : 0 < G)
    (hM : 0 < M) (hx : x ∈ schwarzschildDomain G c M) (a i j k : Fin 4) :
    riemann (schwarzschildMetric G c M) x a i j k = schwarzschildRiemannExpr G c M x a i j k := by
  have h1 := (schwarzschildDomain.pos hG hM hx).ne'
  have h2 := (schwarzschildDomain.sub_pos hx).ne'
  have h3 := (schwarzschildDomain.sin_pos hx).ne'
  have hcongr : ∀ a i j : Fin 4, (fun y => christoffel (schwarzschildMetric G c M) y a i j)
      =ᶠ[nhds x] fun y =>
        schwarzschildGammaR G c M a i j (y 1) * schwarzschildGammaTheta a i j (y 2) :=
    fun a i j => by
      filter_upwards [(isOpen_schwarzschildDomain G c M).mem_nhds hx] with y hy
      exact christoffel_schwarzschild hG hM hy a i j
  have hR : ∀ a i j, HasDerivAt (schwarzschildGammaR G c M a i j)
      (schwarzschildGammaR' G c M a i j (x 1)) (x 1) := hasDerivAt_gammaR h1 h2
  have hT : ∀ a i j, HasDerivAt (schwarzschildGammaTheta a i j)
      (schwarzschildGammaTheta' a i j (x 2)) (x 2) := hasDerivAt_gammaTheta h3
  have hD : ∀ a i j e, coordDeriv (fun y => christoffel (schwarzschildMetric G c M) y a i j) x e
      = (if e = 1 then schwarzschildGammaR' G c M a i j (x 1) else 0)
          * schwarzschildGammaTheta a i j (x 2)
        + schwarzschildGammaR G c M a i j (x 1)
          * (if e = 2 then schwarzschildGammaTheta' a i j (x 2) else 0) := fun a i j e => by
    rw [coordDeriv_congr (hcongr a i j) e, coordDeriv_proj_mul 1 2 (hR a i j).differentiableAt
      (hT a i j).differentiableAt, (hR a i j).deriv, (hT a i j).deriv]
  unfold riemann schwarzschildRiemannExpr
  rw [hD, hD]
  simp only [christoffel_schwarzschild hG hM hx]

/-- The component `a = 0` of `riemann_schwarzschild_expr` agrees with the closed form. -/
lemma schwarzschildRiemannExpr_zero {G : ℝ} {c : SpeedOfLight} {M : ℝ} {x : Fin 4 → ℝ}
    (hG : 0 < G) (hM : 0 < M) (hx : x ∈ schwarzschildDomain G c M) (i j k : Fin 4) :
    schwarzschildRiemannExpr G c M x 0 i j k = schwarzschildRiemann G c M x 0 i j k := by
  have hc := c.val_ne_zero
  have h1 := (schwarzschildDomain.pos hG hM hx).ne'
  have h2 := (schwarzschildDomain.sub_pos hx).ne'
  have h3 := (schwarzschildDomain.sin_pos hx).ne'
  have h4 := (schwarzschildDomain.one_sub_pos hG hM hx).ne'
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
  simp [Fin.sum_univ_four, schwarzschildRiemannExpr, schwarzschildGammaR, schwarzschildGammaR',
    schwarzschildGammaTheta, schwarzschildGammaTheta', schwarzschildRiemann,
    schwarzschildCurvature, schwarzschildMetric]
  all_goals (field_simp; ring1)

/-- The component `a = 1` of `riemann_schwarzschild_expr` agrees with the closed form. -/
lemma schwarzschildRiemannExpr_one {G : ℝ} {c : SpeedOfLight} {M : ℝ} {x : Fin 4 → ℝ}
    (hG : 0 < G) (hM : 0 < M) (hx : x ∈ schwarzschildDomain G c M) (i j k : Fin 4) :
    schwarzschildRiemannExpr G c M x 1 i j k = schwarzschildRiemann G c M x 1 i j k := by
  have hc := c.val_ne_zero
  have h1 := (schwarzschildDomain.pos hG hM hx).ne'
  have h2 := (schwarzschildDomain.sub_pos hx).ne'
  have h3 := (schwarzschildDomain.sin_pos hx).ne'
  have h4 := (schwarzschildDomain.one_sub_pos hG hM hx).ne'
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
  simp [Fin.sum_univ_four, schwarzschildRiemannExpr, schwarzschildGammaR, schwarzschildGammaR',
    schwarzschildGammaTheta, schwarzschildGammaTheta', schwarzschildRiemann,
    schwarzschildCurvature, schwarzschildMetric]
  all_goals (field_simp; ring1)

/-- The component `a = 2` of `riemann_schwarzschild_expr` agrees with the closed form. -/
lemma schwarzschildRiemannExpr_two {G : ℝ} {c : SpeedOfLight} {M : ℝ} {x : Fin 4 → ℝ}
    (hG : 0 < G) (hM : 0 < M) (hx : x ∈ schwarzschildDomain G c M) (i j k : Fin 4) :
    schwarzschildRiemannExpr G c M x 2 i j k = schwarzschildRiemann G c M x 2 i j k := by
  have hc := c.val_ne_zero
  have h1 := (schwarzschildDomain.pos hG hM hx).ne'
  have h2 := (schwarzschildDomain.sub_pos hx).ne'
  have h3 := (schwarzschildDomain.sin_pos hx).ne'
  have h4 := (schwarzschildDomain.one_sub_pos hG hM hx).ne'
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
  simp [Fin.sum_univ_four, schwarzschildRiemannExpr, schwarzschildGammaR, schwarzschildGammaR',
    schwarzschildGammaTheta, schwarzschildGammaTheta', schwarzschildRiemann,
    schwarzschildCurvature, schwarzschildMetric]
  all_goals first | (field_simp; ring1) | field_simp

/-- The component `a = 3` of `riemann_schwarzschild_expr` agrees with the closed form. -/
lemma schwarzschildRiemannExpr_three {G : ℝ} {c : SpeedOfLight} {M : ℝ} {x : Fin 4 → ℝ}
    (hG : 0 < G) (hM : 0 < M) (hx : x ∈ schwarzschildDomain G c M) (i j k : Fin 4) :
    schwarzschildRiemannExpr G c M x 3 i j k = schwarzschildRiemann G c M x 3 i j k := by
  have hc := c.val_ne_zero
  have h1 := (schwarzschildDomain.pos hG hM hx).ne'
  have h2 := (schwarzschildDomain.sub_pos hx).ne'
  have h3 := (schwarzschildDomain.sin_pos hx).ne'
  have h4 := (schwarzschildDomain.one_sub_pos hG hM hx).ne'
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
  simp [Fin.sum_univ_four, schwarzschildRiemannExpr, schwarzschildGammaR, schwarzschildGammaR',
    schwarzschildGammaTheta, schwarzschildGammaTheta', schwarzschildRiemann,
    schwarzschildCurvature, schwarzschildMetric]
  all_goals first | (field_simp; ring1) | (field_simp; simp only [cos_sq']; ring1) | field_simp

/-- The Riemann tensor of the Schwarzschild metric on the exterior region. -/
lemma riemann_schwarzschild {G : ℝ} {c : SpeedOfLight} {M : ℝ} {x : Fin 4 → ℝ} (hG : 0 < G)
    (hM : 0 < M) (hx : x ∈ schwarzschildDomain G c M) (a i j k : Fin 4) :
    riemann (schwarzschildMetric G c M) x a i j k = schwarzschildRiemann G c M x a i j k := by
  rw [riemann_schwarzschild_expr hG hM hx]
  fin_cases a
  exacts [schwarzschildRiemannExpr_zero hG hM hx i j k, schwarzschildRiemannExpr_one hG hM hx i j k,
    schwarzschildRiemannExpr_two hG hM hx i j k, schwarzschildRiemannExpr_three hG hM hx i j k]

/-!

## C. Vacuum

-/

/-- The Schwarzschild metric is a vacuum solution: its Ricci tensor vanishes. -/
theorem ricci_schwarzschild {G : ℝ} {c : SpeedOfLight} {M : ℝ} {x : Fin 4 → ℝ} (hG : 0 < G)
    (hM : 0 < M) (hx : x ∈ schwarzschildDomain G c M) (i j : Fin 4) :
    ricci (schwarzschildMetric G c M) x i j = 0 := by
  simp only [ricci, riemann_schwarzschild hG hM hx]
  fin_cases i <;> fin_cases j <;>
  simp [Fin.sum_univ_four, schwarzschildRiemann, schwarzschildCurvature]
  all_goals ring

/-- The Ricci scalar of the Schwarzschild metric vanishes. -/
lemma ricciScalar_schwarzschild {G : ℝ} {c : SpeedOfLight} {M : ℝ} {x : Fin 4 → ℝ} (hG : 0 < G)
    (hM : 0 < M) (hx : x ∈ schwarzschildDomain G c M) :
    ricciScalar (schwarzschildMetric G c M) x = 0 := by
  simp [ricciScalar, ricci_schwarzschild hG hM hx]

/-- The Einstein tensor of the Schwarzschild metric vanishes. -/
lemma einstein_schwarzschild {G : ℝ} {c : SpeedOfLight} {M : ℝ} {x : Fin 4 → ℝ} (hG : 0 < G)
    (hM : 0 < M) (hx : x ∈ schwarzschildDomain G c M) (a b : Fin 4) :
    einstein (schwarzschildMetric G c M) x a b = 0 := by
  simp [einstein, ricci_schwarzschild hG hM hx, ricciScalar_schwarzschild hG hM hx]

/-!

## D. The Kretschmann scalar

-/

/-- The Kretschmann scalar of the Schwarzschild metric is `48 G² M² / (c⁴ r⁶)`. -/
theorem kretschmann_schwarzschild {G : ℝ} {c : SpeedOfLight} {M : ℝ} {x : Fin 4 → ℝ} (hG : 0 < G)
    (hM : 0 < M) (hx : x ∈ schwarzschildDomain G c M) :
    kretschmann (schwarzschildMetric G c M) x = 48 * G ^ 2 * M ^ 2 / ((c : ℝ) ^ 4 * x 1 ^ 6) := by
  have hc := c.val_ne_zero
  have h1 := (schwarzschildDomain.pos hG hM hx).ne'
  have h2 := (schwarzschildDomain.sub_pos hx).ne'
  have h3 := (schwarzschildDomain.sin_pos hx).ne'
  have h4 := (schwarzschildDomain.one_sub_pos hG hM hx).ne'
  have hrs : 48 * G ^ 2 * M ^ 2 / ((c : ℝ) ^ 4 * x 1 ^ 6)
      = 12 * schwarzschildRadius G c M ^ 2 / x 1 ^ 6 := by
    unfold schwarzschildRadius
    field_simp
    ring
  rw [hrs, kretschmann_diagonal (g := schwarzschildMetric G c M) rfl
    (schwarzschildMetric_inv hG hM hx)]
  simp only [riemann_schwarzschild hG hM hx]
  simp [Fin.sum_univ_four, schwarzschildRiemann, schwarzschildCurvature, schwarzschildMetric]
  field_simp
  ring

end GeneralRelativity
