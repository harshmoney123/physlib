/-
Copyright (c) 2026 Harsha Vankayalapati. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harsha Vankayalapati
-/
module

public import PhyslibAlpha.Relativity.General.MorrisThorne.Metric

/-!

# The Morris-Thorne metric with a redshift function

The Morris-Thorne metric with an arbitrary smooth redshift function `Φ` and its Christoffel
symbols.

## i. Overview

The Morris-Thorne metric with redshift function `Φ(r)` and shape function `b(r)` is
`-e^{2Φ(r)} dt² + (1 - b(r)/r)⁻¹ dr² + r² dθ² + r² sin²θ dφ²`
(`morrisThorneRedshiftMetric`). It is a Lorentzian metric on the region `morrisThorneDomain b`
(`isLorentzianMetricOn_morrisThorneRedshiftMetric`), which does not depend on `Φ`. For `Φ = 0` it
is `morrisThorneMetric`.

Its Christoffel symbols factorize as an `r`-dependent factor `morrisThorneRedshiftGammaR` times the
`θ`-dependent factor `schwarzschildGammaTheta` of the Schwarzschild metric
(`christoffel_morrisThorneRedshift`).

## ii. Key results

- `morrisThorneRedshiftMetric` : the metric field.
- `isLorentzianMetricOn_morrisThorneRedshiftMetric` : it is Lorentzian on `morrisThorneDomain b`.
- `morrisThorneRedshiftMetric_inv` : the inverse metric.
- `christoffel_morrisThorneRedshift` : the Christoffel symbols.

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

/-- The Morris-Thorne metric
`-e^{2Φ(r)} dt² + (1 - b(r)/r)⁻¹ dr² + r² dθ² + r² sin²θ dφ²` with redshift function `Φ` and
shape function `b`, in coordinates `(t, r, θ, φ)` and units `G = c = 1`. -/
def morrisThorneRedshiftMetric (Φ b : ℝ → ℝ) : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ :=
  fun y => Matrix.diagonal
    ![-exp (2 * Φ (y 1)), (1 - b (y 1) / y 1)⁻¹, y 1 ^ 2, y 1 ^ 2 * sin (y 2) ^ 2]

section Lorentzian

variable {Φ b : ℝ → ℝ} {x : Fin 4 → ℝ}

/-- The Morris-Thorne metric with a redshift function is a Lorentzian metric on the region
outside the throat. -/
lemma isLorentzianMetricOn_morrisThorneRedshiftMetric (hΦ : ContDiff ℝ ∞ Φ)
    (hb : ContDiff ℝ ∞ b) :
    IsLorentzianMetricOn (morrisThorneRedshiftMetric Φ b) (morrisThorneDomain b) where
  isOpen := isOpen_morrisThorneDomain hb.continuous
  symm _ _ := Matrix.isSymm_diagonal _
  contDiffOn a c := by
    unfold morrisThorneRedshiftMetric
    intro y hy
    have h1 := morrisThorneDomain.pos hy
    have h2 := morrisThorneDomain.one_sub_pos hy
    have hbr : ContDiffAt ℝ ∞ (fun y : Fin 4 → ℝ => b (y 1)) y :=
      (hb.comp (by fun_prop : ContDiff ℝ ∞ fun y : Fin 4 → ℝ => y 1)).contDiffAt
    have hΦr : ContDiffAt ℝ ∞ (fun y : Fin 4 → ℝ => Φ (y 1)) y :=
      (hΦ.comp (by fun_prop : ContDiff ℝ ∞ fun y : Fin 4 → ℝ => y 1)).contDiffAt
    by_cases hac : a = c
    · subst hac
      refine ContDiffAt.contDiffWithinAt ?_
      fin_cases a <;> simp [Matrix.diagonal_apply_eq]
      · exact ContDiffAt.neg (ContDiffAt.exp (contDiffAt_const.mul hΦr))
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
      positivity
    · simpa using h2
    · show (0 : ℝ) < y 1 ^ 2
      positivity
    · simp; positivity

/-- The inverse of the Morris-Thorne metric with a redshift function. -/
lemma morrisThorneRedshiftMetric_inv {y : Fin 4 → ℝ} (hy : y ∈ morrisThorneDomain b) :
    (morrisThorneRedshiftMetric Φ b y)⁻¹ = Matrix.diagonal
      ![-(exp (2 * Φ (y 1)))⁻¹, 1 - b (y 1) / y 1, (y 1 ^ 2)⁻¹, (y 1 ^ 2 * sin (y 2) ^ 2)⁻¹] := by
  have h1 := (morrisThorneDomain.pos hy).ne'
  have h3 := (morrisThorneDomain.sin_pos hy).ne'
  have h4 := (morrisThorneDomain.one_sub_pos hy).ne'
  have h5 := (morrisThorneDomain.sub_pos hy).ne'
  refine Matrix.inv_eq_right_inv ?_
  rw [morrisThorneRedshiftMetric, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp <;> field_simp

end Lorentzian

/-!

## B. Closed form of the Christoffel symbols

-/

/-- The `r`-dependent factor of the Christoffel symbol `Γ^a_{ij}` of the Morris-Thorne metric with
redshift function `Φ`. The `θ`-dependent factor is `schwarzschildGammaTheta a i j`. -/
def morrisThorneRedshiftGammaR (Φ b : ℝ → ℝ) (a i j : Fin 4) : ℝ → ℝ :=
  if a = 0 ∧ ((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)) then fun r => deriv Φ r
  else if a = 1 ∧ i = 0 ∧ j = 0 then
    fun r => exp (2 * Φ r) * deriv Φ r * ((r - b r) / r)
  else morrisThorneGammaR b a i j

/-- The `r`-derivative of `morrisThorneRedshiftGammaR`. -/
def morrisThorneRedshiftGammaR' (Φ b : ℝ → ℝ) (a i j : Fin 4) : ℝ → ℝ :=
  if a = 0 ∧ ((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)) then fun r => deriv (deriv Φ) r
  else if a = 1 ∧ i = 0 ∧ j = 0 then
    fun r => exp (2 * Φ r) * (2 * deriv Φ r ^ 2 * ((r - b r) / r)
      + deriv (deriv Φ) r * ((r - b r) / r) + deriv Φ r * ((b r - r * deriv b r) / r ^ 2))
  else morrisThorneGammaR' b a i j

/-!

## C. Derivatives of the Christoffel symbols

-/

section Derivatives

variable {Φ b : ℝ → ℝ} {r : ℝ}

lemma hasDerivAt_morrisThorneRedshiftGammaR_trr (hΦ : ContDiff ℝ ∞ Φ) (r : ℝ) :
    HasDerivAt (deriv Φ) (deriv (deriv Φ) r) r :=
  ((contDiff_infty_iff_deriv.mp hΦ).2.differentiable (by simp) r).hasDerivAt

lemma hasDerivAt_morrisThorneRedshiftGammaR_rtt (hΦ : ContDiff ℝ ∞ Φ) (hb : ContDiff ℝ ∞ b)
    (hr : r ≠ 0) :
    HasDerivAt (fun r => exp (2 * Φ r) * deriv Φ r * ((r - b r) / r))
      (exp (2 * Φ r) * (2 * deriv Φ r ^ 2 * ((r - b r) / r)
        + deriv (deriv Φ) r * ((r - b r) / r) + deriv Φ r * ((b r - r * deriv b r) / r ^ 2)))
      r := by
  have hΦ1 : HasDerivAt Φ (deriv Φ r) r := (hΦ.differentiable (by simp) r).hasDerivAt
  have hb1 : HasDerivAt b (deriv b r) r := (hb.differentiable (by simp) r).hasDerivAt
  have hE : HasDerivAt (fun r => exp (2 * Φ r)) (exp (2 * Φ r) * (2 * deriv Φ r)) r :=
    (hΦ1.const_mul 2).exp
  have hF : HasDerivAt (fun r => (r - b r) / r) ((b r - r * deriv b r) / r ^ 2) r := by
    have := ((hasDerivAt_id' r).fun_sub hb1).fun_div (hasDerivAt_id' r) hr
    refine this.congr_deriv ?_
    field_simp
    ring
  have := (hE.fun_mul (hasDerivAt_morrisThorneRedshiftGammaR_trr hΦ r)).fun_mul hF
  refine this.congr_deriv ?_
  ring

lemma hasDerivAt_morrisThorneRedshiftGammaR (hΦ : ContDiff ℝ ∞ Φ) (hb : ContDiff ℝ ∞ b)
    (hr : r ≠ 0) (h2 : r - b r ≠ 0) (a i j : Fin 4) :
    HasDerivAt (morrisThorneRedshiftGammaR Φ b a i j) (morrisThorneRedshiftGammaR' Φ b a i j r)
      r := by
  unfold morrisThorneRedshiftGammaR morrisThorneRedshiftGammaR'
  split_ifs
  · exact hasDerivAt_morrisThorneRedshiftGammaR_trr hΦ r
  · exact hasDerivAt_morrisThorneRedshiftGammaR_rtt hΦ hb hr
  · exact hasDerivAt_morrisThorneGammaR hb hr h2 a i j

end Derivatives

/-!

## D. Derivatives of the metric

-/

section Entries

variable {Φ b : ℝ → ℝ} {x : Fin 4 → ℝ} {p q : Fin 4}

lemma coordDeriv_morrisThorneRedshiftMetric_tt (hΦ : ContDiff ℝ ∞ Φ) (c : Fin 4) :
    coordDeriv (fun y => morrisThorneRedshiftMetric Φ b y 0 0) x c
      = if c = 1 then -(exp (2 * Φ (x 1)) * (2 * deriv Φ (x 1))) else 0 := by
  have hA : HasDerivAt (fun r : ℝ => -exp (2 * Φ r)) (-(exp (2 * Φ (x 1)) * (2 * deriv Φ (x 1))))
      (x 1) :=
    (((hΦ.differentiable (by simp) (x 1)).hasDerivAt.const_mul 2).exp).neg
  have : (fun y => morrisThorneRedshiftMetric Φ b y 0 0)
      = fun y => (fun r : ℝ => -exp (2 * Φ r)) (y 1) := by
    funext y; simp [morrisThorneRedshiftMetric]
  rw [this, coordDeriv_comp_proj 1 hA.differentiableAt, hA.deriv]

lemma coordDeriv_morrisThorneRedshiftMetric_rr (c : Fin 4) :
    coordDeriv (fun y => morrisThorneRedshiftMetric Φ b y 1 1) x c
      = coordDeriv (fun y => morrisThorneMetric b y 1 1) x c := rfl

lemma coordDeriv_morrisThorneRedshiftMetric_θθ (c : Fin 4) :
    coordDeriv (fun y => morrisThorneRedshiftMetric Φ b y 2 2) x c = if c = 1 then 2 * x 1 else 0 :=
  coordDeriv_morrisThorneMetric_θθ c

lemma coordDeriv_morrisThorneRedshiftMetric_φφ (c : Fin 4) :
    coordDeriv (fun y => morrisThorneRedshiftMetric Φ b y 3 3) x c
      = (if c = 1 then 2 * x 1 else 0) * sin (x 2) ^ 2
        + x 1 ^ 2 * (if c = 2 then 2 * (sin (x 2) * cos (x 2)) else 0) :=
  coordDeriv_morrisThorneMetric_φφ c

lemma coordDeriv_morrisThorneRedshiftMetric_offDiag (hpq : p ≠ q) (c : Fin 4) :
    coordDeriv (fun y => morrisThorneRedshiftMetric Φ b y p q) x c = 0 := by
  simp [morrisThorneRedshiftMetric, Matrix.diagonal_apply_ne _ hpq, coordDeriv]

end Entries

/-!

## E. The Christoffel symbols

-/

/-- The Christoffel symbols of the Morris-Thorne metric with a redshift function. -/
lemma christoffel_morrisThorneRedshift {Φ b : ℝ → ℝ} {x : Fin 4 → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    (hb : ContDiff ℝ ∞ b) (hx : x ∈ morrisThorneDomain b) (a i j : Fin 4) :
    christoffel (morrisThorneRedshiftMetric Φ b) x a i j
      = morrisThorneRedshiftGammaR Φ b a i j (x 1) * schwarzschildGammaTheta a i j (x 2) := by
  have h1 := (morrisThorneDomain.pos hx).ne'
  have h2 := (morrisThorneDomain.sub_pos hx).ne'
  have h3 := (morrisThorneDomain.sin_pos hx).ne'
  have h4 := (morrisThorneDomain.one_sub_pos hx).ne'
  fin_cases a <;> fin_cases i <;> fin_cases j <;>
  simp [christoffel, christoffelFirstKind, morrisThorneRedshiftMetric_inv hx,
    Matrix.diagonal_apply, coordDeriv_morrisThorneRedshiftMetric_tt hΦ,
    coordDeriv_morrisThorneRedshiftMetric_rr, coordDeriv_morrisThorneMetric_rr hb hx,
    coordDeriv_morrisThorneRedshiftMetric_θθ, coordDeriv_morrisThorneRedshiftMetric_φφ,
    coordDeriv_morrisThorneRedshiftMetric_offDiag, morrisThorneRedshiftGammaR,
    morrisThorneGammaR, schwarzschildGammaTheta]
  all_goals first | (field_simp; ring) | field_simp

end GeneralRelativity
