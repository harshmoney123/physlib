/-
Copyright (c) 2026 Harsha Vankayalapati. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harsha Vankayalapati
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import PhyslibAlpha.Relativity.General.PointwiseCausality

/-!

# Coordinate description of a curved spacetime metric

A Lorentzian metric field on an open set of `Fin 4 → ℝ` and its Christoffel symbols.

## i. Overview

In a single coordinate chart a spacetime metric is a field `g : (Fin 4 → ℝ) → Matrix (Fin 4)
(Fin 4) ℝ` of matrices `g x = g_{μν}(x)`. We say that `g` is a Lorentzian metric on an open set `U`
(`IsLorentzianMetricOn`) if it is symmetric, smooth, and of signature `(-,+,+,+)` at every point of
`U`. Non-degeneracy follows from the signature (`IsLorentzianMetricOn.det_ne_zero`).

The Christoffel symbols of the second kind are
`Γ^a_{bc} = 1/2 g^{ad} (∂_b g_{dc} + ∂_c g_{bd} - ∂_d g_{bc})`,
where `g^{ad}` is the matrix inverse and `∂_b` is the coordinate derivative, computed with `fderiv`
componentwise.

## ii. Key results

- `IsLorentzianMetricOn` : the metric field is symmetric, smooth and Lorentzian on an open set.
- `isLorentzian_diagonal_four` : a diagonal matrix of signs `(-,+,+,+)` is Lorentzian.
- `IsLorentzianMetricOn.det_ne_zero` : a Lorentzian metric is non-degenerate.
- `christoffel` : the Christoffel symbols of the second kind.
- `christoffel_symm` : `Γ^a_{bc} = Γ^a_{cb}`.
- `sum_metric_mul_christoffel` : lowering the index recovers the first-kind symbols.
- `christoffel_const` : the Christoffel symbols of a constant metric vanish.
- `minkowskiField` : the constant Minkowski metric field, with
  `isLorentzianMetricOn_minkowskiField` and `christoffel_minkowskiField`.

## iii. Table of contents

- A. Metric fields
- B. Christoffel symbols
- C. Symmetry and constant metrics
- D. The Minkowski metric field

## iv. References

- B. O'Neill, *Semi-Riemannian Geometry*, Chapter 3.

-/

@[expose] public section

noncomputable section

namespace GeneralRelativity

open scoped ContDiff

/-!

## A. Metric fields

-/

/-- A metric field `g` is a Lorentzian metric on the open set `U` of coordinates if it is
symmetric, smooth and of signature `(-,+,+,+)` at each point of `U`. -/
structure IsLorentzianMetricOn (g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ)
    (U : Set (Fin 4 → ℝ)) : Prop where
  /-- The coordinate domain is open. -/
  isOpen : IsOpen U
  /-- The metric is symmetric. -/
  symm : ∀ x ∈ U, (g x).IsSymm
  /-- Each component of the metric is smooth. -/
  contDiffOn : ∀ a b, ContDiffOn ℝ ∞ (fun x => g x a b) U
  /-- The metric has signature `(-,+,+,+)`. -/
  lorentzian : ∀ x ∈ U, IsLorentzian (Matrix.toBilin' (g x))

/-- A Lorentzian bilinear form given by a matrix has non-zero determinant. -/
lemma IsLorentzian.det_ne_zero {G : Matrix (Fin 4) (Fin 4) ℝ}
    (hG : IsLorentzian (Matrix.toBilin' G)) : G.det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hGv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  obtain ⟨u, hu, horth⟩ := hG.exists_timelike
  have h1 : Matrix.toBilin' G u v = 0 := by
    simp [Matrix.toBilin'_apply', hGv]
  have h2 := horth v h1 hv
  have h3 : Matrix.toBilin' G v v = 0 := by
    simp [Matrix.toBilin'_apply', hGv]
  linarith

/-- A diagonal matrix with entries of signs `(-,+,+,+)` is Lorentzian. -/
lemma isLorentzian_diagonal_four {w : Fin 4 → ℝ} (h0 : w 0 < 0) (h1 : 0 < w 1) (h2 : 0 < w 2)
    (h3 : 0 < w 3) : IsLorentzian (Matrix.toBilin' (Matrix.diagonal w)) := by
  have hb : ∀ v u : Fin 4 → ℝ, Matrix.toBilin' (Matrix.diagonal w) v u
      = w 0 * (v 0 * u 0) + w 1 * (v 1 * u 1) + w 2 * (v 2 * u 2) + w 3 * (v 3 * u 3) := by
    intro v u
    simp [Matrix.toBilin'_apply', dotProduct, Matrix.mulVec_diagonal, Fin.sum_univ_four]
    ring
  refine ⟨fun v u => by simp only [hb]; ring, Pi.single 0 1, ?_, fun v h hv => ?_⟩
  · rw [hb]; simpa using h0
  · simp only [hb, Pi.single_apply] at h
    simp at h
    have hv0 : v 0 = 0 := by
      rcases h with h | h
      · exact absurd h h0.ne
      · exact h
    have hne : v 1 ≠ 0 ∨ v 2 ≠ 0 ∨ v 3 ≠ 0 := by
      by_contra hcon
      simp only [not_or, not_not] at hcon
      refine hv (funext fun i => ?_)
      fin_cases i <;> simp [hv0, hcon]
    rw [hb, hv0]
    have a1 := mul_nonneg h1.le (mul_self_nonneg (v 1))
    have a2 := mul_nonneg h2.le (mul_self_nonneg (v 2))
    have a3 := mul_nonneg h3.le (mul_self_nonneg (v 3))
    rcases hne with h' | h' | h'
    · have := mul_pos h1 (mul_self_pos.2 h'); simp; linarith
    · have := mul_pos h2 (mul_self_pos.2 h'); simp; linarith
    · have := mul_pos h3 (mul_self_pos.2 h'); simp; linarith

/-- A Lorentzian metric field is non-degenerate at every point of its domain. -/
lemma IsLorentzianMetricOn.det_ne_zero {g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
    {U : Set (Fin 4 → ℝ)} (hg : IsLorentzianMetricOn g U) {x : Fin 4 → ℝ} (hx : x ∈ U) :
    (g x).det ≠ 0 :=
  IsLorentzian.det_ne_zero (hg.lorentzian x hx)

/-!

## B. Christoffel symbols

-/

/-- The coordinate derivative `∂_b f` of a real function on `Fin 4 → ℝ`. -/
def coordDeriv (f : (Fin 4 → ℝ) → ℝ) (x : Fin 4 → ℝ) (b : Fin 4) : ℝ :=
  fderiv ℝ f x (Pi.single b 1)

/-- The Christoffel symbols of the first kind
`Γ_{d,bc} = 1/2 (∂_b g_{dc} + ∂_c g_{bd} - ∂_d g_{bc})`. -/
def christoffelFirstKind (g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ) (x : Fin 4 → ℝ)
    (d b c : Fin 4) : ℝ :=
  (coordDeriv (fun y => g y d c) x b + coordDeriv (fun y => g y b d) x c
    - coordDeriv (fun y => g y b c) x d) / 2

/-- The Christoffel symbols of the second kind `Γ^a_{bc} = g^{ad} Γ_{d,bc}`, using the inverse
matrix of the metric. -/
def christoffel (g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ) (x : Fin 4 → ℝ)
    (a b c : Fin 4) : ℝ :=
  ∑ d, (g x)⁻¹ a d * christoffelFirstKind g x d b c

/-!

## C. Symmetry and constant metrics

-/

lemma christoffelFirstKind_symm {g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
    {U : Set (Fin 4 → ℝ)} (hg : IsLorentzianMetricOn g U) {x : Fin 4 → ℝ} (hx : x ∈ U)
    (d b c : Fin 4) : christoffelFirstKind g x d b c = christoffelFirstKind g x d c b := by
  have hev : ∀ p q : Fin 4, (fun y => g y p q) =ᶠ[nhds x] fun y => g y q p := fun p q => by
    filter_upwards [hg.isOpen.mem_nhds hx] with y hy
    exact congrFun (congrFun (hg.symm y hy) p) q |>.symm
  have h1 := (hev d c).fderiv_eq (𝕜 := ℝ)
  have h2 := (hev b d).fderiv_eq (𝕜 := ℝ)
  have h3 := (hev b c).fderiv_eq (𝕜 := ℝ)
  simp only [christoffelFirstKind, coordDeriv, h3, h1, h2] at *
  ring

/-- The Christoffel symbols of a Lorentzian metric are symmetric in their lower indices. -/
lemma christoffel_symm {g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ} {U : Set (Fin 4 → ℝ)}
    (hg : IsLorentzianMetricOn g U) {x : Fin 4 → ℝ} (hx : x ∈ U) (a b c : Fin 4) :
    christoffel g x a b c = christoffel g x a c b := by
  simp [christoffel, christoffelFirstKind_symm hg hx]

/-- Lowering the upper index of the Christoffel symbol recovers the first kind:
`g_{da} Γ^a_{bc} = Γ_{d,bc}`. -/
lemma sum_metric_mul_christoffel {g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
    {U : Set (Fin 4 → ℝ)} (hg : IsLorentzianMetricOn g U) {x : Fin 4 → ℝ} (hx : x ∈ U)
    (d b c : Fin 4) : ∑ a, g x d a * christoffel g x a b c = christoffelFirstKind g x d b c := by
  have h : g x * (g x)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (hg.det_ne_zero hx))
  have key : ∀ e, ∑ a, g x d a * (g x)⁻¹ a e = if d = e then 1 else 0 := fun e => by
    simpa [Matrix.mul_apply, Matrix.one_apply] using congrFun (congrFun h d) e
  simp only [christoffel, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp [← mul_assoc, ← Finset.sum_mul, key]

/-- The Christoffel symbols of a constant metric field vanish. -/
lemma christoffel_const (G : Matrix (Fin 4) (Fin 4) ℝ) (x : Fin 4 → ℝ) (a b c : Fin 4) :
    christoffel (fun _ => G) x a b c = 0 := by
  simp [christoffel, christoffelFirstKind, coordDeriv]

/-!

## D. The Minkowski metric field

-/

/-- The constant Minkowski metric field `diag(-1, 1, 1, 1)`. -/
def minkowskiField : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ :=
  fun _ => Matrix.diagonal ![-1, 1, 1, 1]

/-- The bilinear form of the Minkowski metric field in components. -/
lemma minkowskiField_bilin (x v w : Fin 4 → ℝ) :
    Matrix.toBilin' (minkowskiField x) v w = -(v 0 * w 0) + v 1 * w 1 + v 2 * w 2 + v 3 * w 3 := by
  simp [minkowskiField, Matrix.toBilin'_apply', dotProduct, Matrix.mulVec_diagonal,
    Fin.sum_univ_four]

/-- The Minkowski metric field is a Lorentzian metric on all of `Fin 4 → ℝ`. -/
lemma isLorentzianMetricOn_minkowskiField : IsLorentzianMetricOn minkowskiField Set.univ where
  isOpen := isOpen_univ
  symm _ _ := Matrix.isSymm_diagonal _
  contDiffOn _ _ := contDiffOn_const
  lorentzian x _ := by
    refine ⟨fun v w => ?_, Pi.single 0 1, ?_, fun v h hv => ?_⟩
    · simp only [minkowskiField_bilin]
      ring
    · rw [minkowskiField_bilin]
      simp
    · simp only [minkowskiField_bilin, Pi.single_eq_same] at h
      have h0 : v 0 = 0 := by simpa [Pi.single_apply] using h
      have hne : v 1 ≠ 0 ∨ v 2 ≠ 0 ∨ v 3 ≠ 0 := by
        by_contra hcon
        simp only [not_or, not_not] at hcon
        refine hv (funext fun i => ?_)
        fin_cases i <;> simp [h0, hcon]
      rw [minkowskiField_bilin, h0]
      rcases hne with h1 | h1 | h1
      · have := sq_pos_of_ne_zero h1; nlinarith [sq_nonneg (v 2), sq_nonneg (v 3)]
      · have := sq_pos_of_ne_zero h1; nlinarith [sq_nonneg (v 1), sq_nonneg (v 3)]
      · have := sq_pos_of_ne_zero h1; nlinarith [sq_nonneg (v 1), sq_nonneg (v 2)]

/-- The Christoffel symbols of the Minkowski metric field vanish. -/
lemma christoffel_minkowskiField (x : Fin 4 → ℝ) (a b c : Fin 4) :
    christoffel minkowskiField x a b c = 0 :=
  christoffel_const _ x a b c

end GeneralRelativity
