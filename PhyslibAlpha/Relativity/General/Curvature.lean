/-
Copyright (c) 2026 Harsha Vankayalapati. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harsha Vankayalapati
-/
module

public import PhyslibAlpha.Relativity.General.CoordinateMetric

/-!

# Curvature of a coordinate spacetime metric

The Riemann, Ricci and Einstein tensors of a metric field on `Fin 4 → ℝ`.

## i. Overview

Given a metric field `g` as in `PhyslibAlpha.Relativity.General.CoordinateMetric`, we define the
Riemann tensor
`R^a_{bcd} = ∂_c Γ^a_{db} - ∂_d Γ^a_{cb} + Γ^a_{ce} Γ^e_{db} - Γ^a_{de} Γ^e_{cb}`,
the Ricci tensor `R_{bd} = R^a_{bad}`, the Ricci scalar `R = g^{bd} R_{bd}` and the Einstein tensor
`G_{ab} = R_{ab} - 1/2 g_{ab} R`.

## ii. Key results

- `riemann` : the Riemann tensor `R^a_{bcd}`.
- `ricci` : the Ricci tensor.
- `ricciScalar` : the Ricci scalar.
- `einstein` : the Einstein tensor.
- `riemann_antisymm` : `R^a_{bcd} = -R^a_{bdc}`.
- `riemann_const`, `ricci_const`, `ricciScalar_const`, `einstein_const` : all of them vanish for a
  constant metric.

## iii. Table of contents

- A. Definitions
- B. Antisymmetry of the Riemann tensor
- C. Constant metrics

## iv. References

- B. O'Neill, *Semi-Riemannian Geometry*, Chapter 3.

-/

@[expose] public section

noncomputable section

namespace GeneralRelativity

/-!

## A. Definitions

-/

/-- The Riemann tensor
`R^a_{bcd} = ∂_c Γ^a_{db} - ∂_d Γ^a_{cb} + Γ^a_{ce} Γ^e_{db} - Γ^a_{de} Γ^e_{cb}`. -/
def riemann (g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ) (x : Fin 4 → ℝ) (a b c d : Fin 4) : ℝ :=
  coordDeriv (fun y => christoffel g y a d b) x c - coordDeriv (fun y => christoffel g y a c b) x d
    + ∑ e, (christoffel g x a c e * christoffel g x e d b
      - christoffel g x a d e * christoffel g x e c b)

/-- The Ricci tensor `R_{bd} = R^a_{bad}`. -/
def ricci (g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ) (x : Fin 4 → ℝ) (b d : Fin 4) : ℝ :=
  ∑ a, riemann g x a b a d

/-- The Ricci scalar `R = g^{bd} R_{bd}`. -/
def ricciScalar (g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ) (x : Fin 4 → ℝ) : ℝ :=
  ∑ b, ∑ d, (g x)⁻¹ b d * ricci g x b d

/-- The Einstein tensor `G_{ab} = R_{ab} - 1/2 g_{ab} R`. -/
def einstein (g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ) (x : Fin 4 → ℝ) (a b : Fin 4) : ℝ :=
  ricci g x a b - g x a b * ricciScalar g x / 2

/-!

## B. Antisymmetry of the Riemann tensor

-/

/-- The Riemann tensor is antisymmetric in its last two indices. -/
lemma riemann_antisymm (g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ) (x : Fin 4 → ℝ)
    (a b c d : Fin 4) : riemann g x a b c d = - riemann g x a b d c := by
  simp only [riemann]
  have h : ∑ e, (christoffel g x a d e * christoffel g x e c b
      - christoffel g x a c e * christoffel g x e d b)
      = - ∑ e, (christoffel g x a c e * christoffel g x e d b
      - christoffel g x a d e * christoffel g x e c b) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun e _ => by ring
  rw [h]
  ring

/-!

## C. Constant metrics

-/

/-- The Riemann tensor of a constant metric field vanishes. -/
lemma riemann_const (G : Matrix (Fin 4) (Fin 4) ℝ) (x : Fin 4 → ℝ) (a b c d : Fin 4) :
    riemann (fun _ => G) x a b c d = 0 := by
  simp [riemann, christoffel_const, coordDeriv]

/-- The Ricci tensor of a constant metric field vanishes. -/
lemma ricci_const (G : Matrix (Fin 4) (Fin 4) ℝ) (x : Fin 4 → ℝ) (b d : Fin 4) :
    ricci (fun _ => G) x b d = 0 := by
  simp [ricci, riemann_const]

/-- The Ricci scalar of a constant metric field vanishes. -/
lemma ricciScalar_const (G : Matrix (Fin 4) (Fin 4) ℝ) (x : Fin 4 → ℝ) :
    ricciScalar (fun _ => G) x = 0 := by
  simp [ricciScalar, ricci_const]

/-- The Einstein tensor of a constant metric field vanishes. -/
lemma einstein_const (G : Matrix (Fin 4) (Fin 4) ℝ) (x : Fin 4 → ℝ) (a b : Fin 4) :
    einstein (fun _ => G) x a b = 0 := by
  simp [einstein, ricci_const, ricciScalar_const]

end GeneralRelativity
