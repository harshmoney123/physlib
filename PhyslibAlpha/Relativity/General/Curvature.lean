/-
Copyright (c) 2026 Harsha Vankayalapati. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harsha Vankayalapati
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Matrix.Normed
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

The Ricci tensor is symmetric for a smooth Lorentzian metric. The only non-algebraic input is the
symmetry of the contracted derivative `∂_d Γ^a_{ab}`. For this we write `Γ^a_{ab}` as the trace
`1/2 g^{ae} ∂_b g_{ea}`, differentiate it using `∂_d g^{-1} = - g^{-1} (∂_d g) g^{-1}`, and use the
cyclicity of the trace together with the symmetry of second derivatives of `g`.

## ii. Key results

- `riemann` : the Riemann tensor `R^a_{bcd}`.
- `ricci` : the Ricci tensor.
- `ricciScalar` : the Ricci scalar.
- `einstein` : the Einstein tensor.
- `riemann_antisymm` : `R^a_{bcd} = -R^a_{bdc}`.
- `ricci_symm` : the Ricci tensor of a Lorentzian metric field is symmetric.
- `einstein_symm` : the Einstein tensor of a Lorentzian metric field is symmetric.
- `riemann_const`, `ricci_const`, `ricciScalar_const`, `einstein_const` : all of them vanish for a
  constant metric.

## iii. Table of contents

- A. Definitions
- B. Antisymmetry of the Riemann tensor
- C. Constant metrics
- D. Calculus with coordinate derivatives
- E. Derivative of the inverse metric
- F. Symmetry of the Ricci tensor

## iv. References

- B. O'Neill, *Semi-Riemannian Geometry*, Chapter 3.

-/

@[expose] public section

noncomputable section

namespace GeneralRelativity

open scoped ContDiff

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

/-!

## D. Calculus with coordinate derivatives

-/

section Calculus

variable {x : Fin 4 → ℝ} {f f' : (Fin 4 → ℝ) → ℝ}

/-- The coordinate derivative of a sum. -/
lemma coordDeriv_add (hf : DifferentiableAt ℝ f x) (hf' : DifferentiableAt ℝ f' x) (b : Fin 4) :
    coordDeriv (fun y => f y + f' y) x b = coordDeriv f x b + coordDeriv f' x b := by
  simp [coordDeriv, fderiv_fun_add hf hf']

/-- The Leibniz rule for the coordinate derivative of a product. -/
lemma coordDeriv_mul (hf : DifferentiableAt ℝ f x) (hf' : DifferentiableAt ℝ f' x) (b : Fin 4) :
    coordDeriv (fun y => f y * f' y) x b = coordDeriv f x b * f' x + f x * coordDeriv f' x b := by
  simp [coordDeriv, fderiv_fun_mul' hf hf']
  ring

/-- The coordinate derivative of a finite sum. -/
lemma coordDeriv_sum {ι : Type*} (s : Finset ι) (F : ι → (Fin 4 → ℝ) → ℝ)
    (h : ∀ i ∈ s, DifferentiableAt ℝ (F i) x) (b : Fin 4) :
    coordDeriv (fun y => ∑ i ∈ s, F i y) x b = ∑ i ∈ s, coordDeriv (F i) x b := by
  simp [coordDeriv, fderiv_fun_sum h]

/-- The coordinate derivative only depends on the germ of the function. -/
lemma coordDeriv_congr (h : f =ᶠ[nhds x] f') (b : Fin 4) :
    coordDeriv f x b = coordDeriv f' x b := by
  simp [coordDeriv, h.fderiv_eq (𝕜 := ℝ)]

/-- The coordinate derivative of a function divided by two. -/
lemma coordDeriv_div_two (hf : DifferentiableAt ℝ f x) (b : Fin 4) :
    coordDeriv (fun y => f y / 2) x b = coordDeriv f x b / 2 := by
  simp only [div_eq_mul_inv, coordDeriv, fderiv_mul_const hf]
  simp [mul_comm]

/-- The coordinate derivative of a constant function vanishes. -/
lemma coordDeriv_const (c : ℝ) (b : Fin 4) : coordDeriv (fun _ => c) x b = 0 := by
  simp [coordDeriv]

/-- The coordinate derivative of a smooth function is smooth. -/
lemma contDiffAt_coordDeriv (hf : ContDiffAt ℝ ∞ f x) (b : Fin 4) :
    ContDiffAt ℝ ∞ (fun y => coordDeriv f y b) x :=
  (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const

/-- Mixed coordinate derivatives of a smooth function commute. -/
lemma coordDeriv_comm (hf : ContDiffAt ℝ ∞ f x) (b d : Fin 4) :
    coordDeriv (fun y => coordDeriv f y b) x d = coordDeriv (fun y => coordDeriv f y d) x b := by
  have hs := hf.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField])
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by simp)).differentiableAt (by simp)
  simp only [coordDeriv]
  rw [fderiv_clm_apply hd (differentiableAt_const _), fderiv_clm_apply hd (differentiableAt_const _)]
  simp [hs.eq (Pi.single b 1) (Pi.single d 1)]

end Calculus

/-!

## E. Derivative of the inverse metric

-/

section Metric

variable {g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ} {U : Set (Fin 4 → ℝ)} {x : Fin 4 → ℝ}

/-- The components of a Lorentzian metric field are smooth at each point of its domain. -/
lemma IsLorentzianMetricOn.contDiffAt (hg : IsLorentzianMetricOn g U) (hx : x ∈ U) (p q : Fin 4) :
    ContDiffAt ℝ ∞ (fun y => g y p q) x :=
  (hg.contDiffOn p q).contDiffAt (hg.isOpen.mem_nhds hx)

/-- The components of the inverse of a Lorentzian metric field are differentiable. -/
lemma IsLorentzianMetricOn.differentiableAt_inv (hg : IsLorentzianMetricOn g U) (hx : x ∈ U)
    (a e : Fin 4) : DifferentiableAt ℝ (fun y => (g y)⁻¹ a e) x := by
  let _ := Matrix.linftyOpNormedRing (n := Fin 4) (α := ℝ)
  let _ := Matrix.linftyOpNormedAlgebra (n := Fin 4) (R := ℝ) (α := ℝ)
  have h1 : DifferentiableAt ℝ g x := differentiableAt_pi.2 fun p => differentiableAt_pi.2 fun q =>
    (hg.contDiffAt hx p q).differentiableAt (by simp)
  have hu : IsUnit (g x) := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2
    (hg.det_ne_zero hx))
  have h2 : DifferentiableAt ℝ (fun y => Ring.inverse (g y)) x := h1.inverse hu
  have h3 : ∀ y, (g y)⁻¹ = Ring.inverse (g y) := fun y => Matrix.nonsing_inv_eq_ringInverse _
  simp only [h3]
  exact differentiableAt_pi.1 (differentiableAt_pi.1 h2 a) e

/-- The components of the Christoffel symbols of a Lorentzian metric field are differentiable. -/
lemma IsLorentzianMetricOn.differentiableAt_christoffel (hg : IsLorentzianMetricOn g U)
    (hx : x ∈ U) (a b c : Fin 4) : DifferentiableAt ℝ (fun y => christoffel g y a b c) x := by
  have hD : ∀ p q r : Fin 4, DifferentiableAt ℝ (fun y => coordDeriv (fun z => g z p q) y r) x :=
    fun p q r => (contDiffAt_coordDeriv (hg.contDiffAt hx p q) r).differentiableAt (by simp)
  have hI := hg.differentiableAt_inv hx
  unfold christoffel christoffelFirstKind
  refine DifferentiableAt.fun_sum fun d _ => (hI a d).mul ?_
  have hs : DifferentiableAt ℝ (fun y => coordDeriv (fun z => g z d c) y b
      + coordDeriv (fun z => g z b d) y c - coordDeriv (fun z => g z b c) y d) x :=
    ((hD d c b).fun_add (hD b d c)).fun_sub (hD b c d)
  simpa only [div_eq_mul_inv] using hs.mul_const (2⁻¹ : ℝ)

/-- The matrix of coordinate derivatives `∂_b g_{pq}` of a metric field. -/
def metricDeriv (g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ) (x : Fin 4 → ℝ) (b : Fin 4) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun p q => coordDeriv (fun y => g y p q) x b

/-- The matrix of coordinate derivatives `∂_d g^{pq}` of the inverse metric field. -/
def inverseMetricDeriv (g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ) (x : Fin 4 → ℝ) (d : Fin 4) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun p q => coordDeriv (fun y => (g y)⁻¹ p q) x d

/-- The derivative of the inverse metric: `∂_d g^{-1} = - g^{-1} (∂_d g) g^{-1}`. -/
lemma inverseMetricDeriv_eq (hg : IsLorentzianMetricOn g U) (hx : x ∈ U) (d : Fin 4) :
    inverseMetricDeriv g x d = -((g x)⁻¹ * metricDeriv g x d * (g x)⁻¹) := by
  have key : metricDeriv g x d * (g x)⁻¹ + g x * inverseMetricDeriv g x d = 0 := by
    ext p e
    have hev : (fun y => ∑ q, g y p q * (g y)⁻¹ q e) =ᶠ[nhds x] fun _ => (1 : Matrix _ _ ℝ) p e := by
      filter_upwards [hg.isOpen.mem_nhds hx] with y hy
      have := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (hg.det_ne_zero hy))
      simpa [Matrix.mul_apply] using congrFun (congrFun this p) e
    have h0 := coordDeriv_congr hev d
    rw [coordDeriv_const, coordDeriv_sum _ (fun q y => g y p q * (g y)⁻¹ q e) (fun q _ =>
      ((hg.contDiffAt hx p q).differentiableAt (by simp)).mul (hg.differentiableAt_inv hx q e))]
      at h0
    simp only [coordDeriv_mul ((hg.contDiffAt hx p _).differentiableAt (by simp))
      (hg.differentiableAt_inv hx _ e), Finset.sum_add_distrib] at h0
    simpa [Matrix.mul_apply, metricDeriv, inverseMetricDeriv] using h0
  have hl : (g x)⁻¹ * g x = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hg.det_ne_zero hx))
  have h1 : inverseMetricDeriv g x d = (g x)⁻¹ * (g x * inverseMetricDeriv g x d) := by
    rw [← Matrix.mul_assoc, hl, Matrix.one_mul]
  rw [h1, eq_neg_of_add_eq_zero_right key, Matrix.mul_neg, Matrix.mul_assoc]

/-!

## F. Symmetry of the Ricci tensor

-/

/-- The contracted Christoffel symbol is a trace:
`Γ^a_{ab} = 1/2 g^{ae} ∂_b g_{ea}`. -/
lemma sum_christoffel_eq (hg : IsLorentzianMetricOn g U) {y : Fin 4 → ℝ} (hy : y ∈ U) (b : Fin 4) :
    ∑ a, christoffel g y a a b
      = (∑ a, ∑ e, (g y)⁻¹ a e * coordDeriv (fun z => g z e a) y b) / 2 := by
  have hs : ∀ a d, (g y)⁻¹ a d = (g y)⁻¹ d a := fun a d => ((hg.symm y hy).inv.apply a d).symm
  have hR : ∑ a, ∑ d, (g y)⁻¹ a d * coordDeriv (fun z => g z a b) y d
      = ∑ a, ∑ d, (g y)⁻¹ a d * coordDeriv (fun z => g z d b) y a := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun a _ => by rw [hs a d]
  have hQ : ∑ a, ∑ d, (g y)⁻¹ a d * coordDeriv (fun z => g z a d) y b
      = ∑ a, ∑ e, (g y)⁻¹ a e * coordDeriv (fun z => g z e a) y b := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun a _ => by rw [hs a d]
  simp only [christoffel, christoffelFirstKind, mul_div_assoc', ← Finset.sum_div, mul_add, mul_sub,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hR, ← hQ]
  ring

/-- The trace of `∂_d g^{-1} · ∂_b g` is symmetric in `b` and `d`. -/
lemma trace_inverseMetricDeriv_symm (hg : IsLorentzianMetricOn g U) (hx : x ∈ U) (b d : Fin 4) :
    (inverseMetricDeriv g x d * metricDeriv g x b).trace
      = (inverseMetricDeriv g x b * metricDeriv g x d).trace := by
  have h : ∀ P Q : Matrix (Fin 4) (Fin 4) ℝ,
      ((g x)⁻¹ * P * (g x)⁻¹ * Q).trace = (((g x)⁻¹ * P) * ((g x)⁻¹ * Q)).trace := by
    intro P Q
    simp [Matrix.mul_assoc]
  rw [inverseMetricDeriv_eq hg hx, inverseMetricDeriv_eq hg hx, Matrix.neg_mul, Matrix.neg_mul,
    Matrix.trace_neg, Matrix.trace_neg, h, h, Matrix.trace_mul_comm]

/-- The derivative of the trace `g^{ae} ∂_b g_{ea}` of the metric. -/
lemma coordDeriv_trace (hg : IsLorentzianMetricOn g U) (hx : x ∈ U) (b d : Fin 4) :
    coordDeriv (fun y => ∑ a, ∑ e, (g y)⁻¹ a e * coordDeriv (fun z => g z e a) y b) x d
      = (inverseMetricDeriv g x d * metricDeriv g x b).trace
        + ∑ a, ∑ e, (g x)⁻¹ a e * coordDeriv (fun y => coordDeriv (fun z => g z e a) y b) x d := by
  have hD : ∀ p q r : Fin 4, DifferentiableAt ℝ (fun y => coordDeriv (fun z => g z p q) y r) x :=
    fun p q r => (contDiffAt_coordDeriv (hg.contDiffAt hx p q) r).differentiableAt (by simp)
  have hI := hg.differentiableAt_inv hx
  have hinner : ∀ a, DifferentiableAt ℝ
      (fun y => ∑ e, (g y)⁻¹ a e * coordDeriv (fun z => g z e a) y b) x := fun a =>
    DifferentiableAt.fun_sum fun e _ => (hI a e).mul (hD e a b)
  rw [coordDeriv_sum _ (fun a y => ∑ e, (g y)⁻¹ a e * coordDeriv (fun z => g z e a) y b)
    (fun a _ => hinner a)]
  have h1 : ∀ a, coordDeriv (fun y => ∑ e, (g y)⁻¹ a e * coordDeriv (fun z => g z e a) y b) x d
      = ∑ e, (coordDeriv (fun y => (g y)⁻¹ a e) x d * coordDeriv (fun z => g z e a) x b
        + (g x)⁻¹ a e * coordDeriv (fun y => coordDeriv (fun z => g z e a) y b) x d) := fun a => by
    rw [coordDeriv_sum _ (fun e y => (g y)⁻¹ a e * coordDeriv (fun z => g z e a) y b)
      (fun e _ => (hI a e).mul (hD e a b))]
    exact Finset.sum_congr rfl fun e _ => coordDeriv_mul (hI a e) (hD e a b) d
  rw [Finset.sum_congr rfl fun a _ => h1 a]
  simp only [Finset.sum_add_distrib]
  simp [Matrix.trace, Matrix.mul_apply, inverseMetricDeriv, metricDeriv, mul_comm]

/-- The contracted derivative `Σ_a ∂_d Γ^a_{ab}` of the Christoffel symbols is symmetric in
`b` and `d`. -/
lemma sum_coordDeriv_christoffel_symm (hg : IsLorentzianMetricOn g U) (hx : x ∈ U) (b d : Fin 4) :
    ∑ a, coordDeriv (fun y => christoffel g y a a b) x d
      = ∑ a, coordDeriv (fun y => christoffel g y a a d) x b := by
  have hD : ∀ p q r : Fin 4, DifferentiableAt ℝ (fun y => coordDeriv (fun z => g z p q) y r) x :=
    fun p q r => (contDiffAt_coordDeriv (hg.contDiffAt hx p q) r).differentiableAt (by simp)
  have hI := hg.differentiableAt_inv hx
  have key : ∀ b d : Fin 4, ∑ a, coordDeriv (fun y => christoffel g y a a b) x d
      = ((inverseMetricDeriv g x d * metricDeriv g x b).trace + ∑ a, ∑ e, (g x)⁻¹ a e
        * coordDeriv (fun y => coordDeriv (fun z => g z e a) y b) x d) / 2 := fun b d => by
    rw [← coordDeriv_sum _ (fun a y => christoffel g y a a b)
      (fun a _ => hg.differentiableAt_christoffel hx a a b)]
    have hev : (fun y => ∑ a, christoffel g y a a b) =ᶠ[nhds x]
        fun y => (∑ a, ∑ e, (g y)⁻¹ a e * coordDeriv (fun z => g z e a) y b) / 2 := by
      filter_upwards [hg.isOpen.mem_nhds hx] with y hy
      exact sum_christoffel_eq hg hy b
    have hW : DifferentiableAt ℝ
        (fun y => ∑ a, ∑ e, (g y)⁻¹ a e * coordDeriv (fun z => g z e a) y b) x :=
      DifferentiableAt.fun_sum fun a _ => DifferentiableAt.fun_sum fun e _ =>
        (hI a e).mul (hD e a b)
    rw [coordDeriv_congr hev, coordDeriv_div_two hW, coordDeriv_trace hg hx]
  have hcomm : ∑ a, ∑ e, (g x)⁻¹ a e * coordDeriv (fun y => coordDeriv (fun z => g z e a) y b) x d
      = ∑ a, ∑ e, (g x)⁻¹ a e * coordDeriv (fun y => coordDeriv (fun z => g z e a) y d) x b :=
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun e _ => by
      rw [coordDeriv_comm (hg.contDiffAt hx e a) b d]
  rw [key b d, key d b, trace_inverseMetricDeriv_symm hg hx b d, hcomm]

/-- The Ricci tensor of a Lorentzian metric field is symmetric. -/
lemma ricci_symm (hg : IsLorentzianMetricOn g U) (hx : x ∈ U) (b d : Fin 4) :
    ricci g x b d = ricci g x d b := by
  have hsymm : ∀ b d : Fin 4, ∀ a, (fun y => christoffel g y a d b)
      =ᶠ[nhds x] fun y => christoffel g y a b d := fun b d a => by
    filter_upwards [hg.isOpen.mem_nhds hx] with y hy
    exact christoffel_symm hg hy a d b
  have hA : ∑ a, coordDeriv (fun y => christoffel g y a d b) x a
      = ∑ a, coordDeriv (fun y => christoffel g y a b d) x a :=
    Finset.sum_congr rfl fun a _ => coordDeriv_congr (hsymm b d a) a
  have hB := sum_coordDeriv_christoffel_symm hg hx b d
  have hC : ∑ a, ∑ e, christoffel g x a a e * christoffel g x e d b
      = ∑ a, ∑ e, christoffel g x a a e * christoffel g x e b d :=
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun e _ => by
      rw [christoffel_symm hg hx e d b]
  have hE : ∑ a, ∑ e, christoffel g x a d e * christoffel g x e a b
      = ∑ a, ∑ e, christoffel g x a b e * christoffel g x e a d := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm, christoffel_symm hg hx j d i, christoffel_symm hg hx i j b]
  simp only [ricci, riemann, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  linarith

/-- The Einstein tensor of a Lorentzian metric field is symmetric. -/
lemma einstein_symm (hg : IsLorentzianMetricOn g U) (hx : x ∈ U) (a b : Fin 4) :
    einstein g x a b = einstein g x b a := by
  simp only [einstein, ricci_symm hg hx a b, (hg.symm x hx).apply a b]

end Metric

end GeneralRelativity
