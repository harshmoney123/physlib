/-
Copyright (c) 2026 Harsha Vankayalapati. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harsha Vankayalapati
-/
module

public import PhyslibAlpha.Relativity.General.ChronologyRelations
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!

# Time functions, chronology and causality

A time function rules out closed causal curves, and Minkowski space is chronological and causal.

## i. Overview

A spacetime `(U, g)` with time orientation `X` is *chronological* if no point lies in its own
chronological future, `p ∉ I⁺(p)`, and *causal* if there is no closed piecewise `C¹`
future-directed causal curve, that is no point `p` with a non-trivial chain of future-directed
causal segments from `p` back to `p`. A causal spacetime is chronological.

A *time function* is a continuous function `f` which strictly increases along every
future-directed causal curve (Hawking and Ellis, Section 6.4). Along a chain of such segments `f`
strictly increases, so a closed chain cannot exist: the existence of a time function implies
that the spacetime is causal (`IsTimeFunctionOn.isCausalSpacetimeOn`).

In Minkowski space with a time orientation `X` whose time component is positive, the coordinate
`x ↦ x 0` is a time function (`isTimeFunctionOn_minkowskiField`). Hence Minkowski space is
causal, and in particular chronological.

## ii. Key results

- `IsChronologicalSpacetimeOn`, `IsCausalSpacetimeOn` : chronology and causality conditions.
- `IsCausalSpacetimeOn.isChronologicalSpacetimeOn` : a causal spacetime is chronological.
- `IsTimeFunctionOn` : a time function.
- `IsTimeFunctionOn.lt_of_mem_chronologicalFuture` : a time function increases strictly from `p`
  to any point of `I⁺(p)`, and weakly to any point of `J⁺(p)`
  (`IsTimeFunctionOn.le_of_mem_causalFuture`).
- `IsTimeFunctionOn.isCausalSpacetimeOn` : the existence of a time function implies causality.
- `not_isClosedFutureCausalCurve_of_isTimeFunctionOn` : there is no closed future-directed
  causal curve when a time function exists.
- `isTimeFunctionOn_minkowskiField` : the time coordinate is a time function on Minkowski space.
- `isCausalSpacetimeOn_minkowskiField`, `isChronologicalSpacetimeOn_minkowskiField` : Minkowski
  space is causal and chronological.

## iii. Table of contents

- A. Chronology and causality conditions
- B. Time functions
- C. Minkowski space is causal and chronological

## iv. References

- S. W. Hawking and G. F. R. Ellis, *The Large Scale Structure of Space-Time*, Section 6.4.

-/

@[expose] public section

noncomputable section

namespace GeneralRelativity

open Set

variable {g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ} {X : (Fin 4 → ℝ) → Fin 4 → ℝ}
  {U : Set (Fin 4 → ℝ)} {γ : ℝ → Fin 4 → ℝ} {a b : ℝ}

/-!

## A. Chronology and causality conditions

-/

/-- The spacetime `(U, g)` with time orientation `X` is chronological: no point lies in its own
chronological future. -/
def IsChronologicalSpacetimeOn (g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ)
    (X : (Fin 4 → ℝ) → Fin 4 → ℝ) (U : Set (Fin 4 → ℝ)) : Prop :=
  ∀ p, p ∉ chronologicalFuture g X U p

/-- The spacetime `(U, g)` with time orientation `X` is causal: there is no closed piecewise `C¹`
future-directed causal curve, that is no non-trivial chain of future-directed causal segments from
a point back to itself. -/
def IsCausalSpacetimeOn (g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ)
    (X : (Fin 4 → ℝ) → Fin 4 → ℝ) (U : Set (Fin 4 → ℝ)) : Prop :=
  ∀ p, ¬ Relation.TransGen (IsFutureCausalStep g X U) p p

lemma isChronologicalSpacetimeOn_iff :
    IsChronologicalSpacetimeOn g X U ↔ chronologyViolatingSet g X U = ∅ := by
  simp [IsChronologicalSpacetimeOn, chronologyViolatingSet, Set.eq_empty_iff_forall_notMem]

/-- A causal spacetime is chronological. -/
lemma IsCausalSpacetimeOn.isChronologicalSpacetimeOn (h : IsCausalSpacetimeOn g X U) :
    IsChronologicalSpacetimeOn g X U := fun p hp =>
  h p (Relation.TransGen.mono (fun _ _ ⟨γ, a, b, hγ, ha, hb⟩ =>
    ⟨γ, a, b, hγ.isFutureCausalCurveOn, ha, hb⟩) _ _ hp)

/-!

## B. Time functions

-/

/-- A time function on `(U, g)` with time orientation `X`: a function `f` which is continuous on
`U` and strictly increasing along every future-directed causal curve. -/
structure IsTimeFunctionOn (g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ)
    (X : (Fin 4 → ℝ) → Fin 4 → ℝ) (U : Set (Fin 4 → ℝ)) (f : (Fin 4 → ℝ) → ℝ) : Prop where
  /-- The function is continuous on `U`. -/
  continuousOn : ContinuousOn f U
  /-- The function is strictly increasing along future-directed causal curves. -/
  strictMonoOn : ∀ (γ : ℝ → Fin 4 → ℝ) (a b : ℝ), IsFutureCausalCurveOn g X U γ a b →
    StrictMonoOn (fun t => f (γ t)) (Icc a b)

namespace IsTimeFunctionOn

variable {f : (Fin 4 → ℝ) → ℝ}

/-- A time function increases strictly along one future-directed causal segment. -/
lemma lt_of_isFutureCausalStep (hf : IsTimeFunctionOn g X U f) {p q : Fin 4 → ℝ}
    (h : IsFutureCausalStep g X U p q) : f p < f q := by
  obtain ⟨γ, a, b, hγ, rfl, rfl⟩ := h
  exact hf.strictMonoOn γ a b hγ (left_mem_Icc.2 hγ.1.1.le) (right_mem_Icc.2 hγ.1.1.le) hγ.1.1

/-- A time function increases strictly from `p` to any point of its chronological future. -/
lemma lt_of_mem_chronologicalFuture (hf : IsTimeFunctionOn g X U f) {p q : Fin 4 → ℝ}
    (h : q ∈ chronologicalFuture g X U p) : f p < f q := by
  have hstep : ∀ {r s : Fin 4 → ℝ}, IsFutureTimelikeStep g X U r s → f r < f s :=
    fun ⟨γ, a, b, hγ, ha, hb⟩ => hf.lt_of_isFutureCausalStep
      ⟨γ, a, b, hγ.isFutureCausalCurveOn, ha, hb⟩
  induction h with
  | single h => exact hstep h
  | tail _ h ih => exact ih.trans (hstep h)

/-- A time function does not decrease from `p` to any point of its causal future. -/
lemma le_of_mem_causalFuture (hf : IsTimeFunctionOn g X U f) {p q : Fin 4 → ℝ}
    (h : q ∈ causalFuture g X U p) : f p ≤ f q := by
  induction h with
  | refl => exact le_rfl
  | tail _ hstep ih => exact ih.trans (hf.lt_of_isFutureCausalStep hstep).le

/-- The existence of a time function implies that the spacetime is causal. -/
lemma isCausalSpacetimeOn (hf : IsTimeFunctionOn g X U f) : IsCausalSpacetimeOn g X U := by
  intro p hp
  have : ∀ {q : Fin 4 → ℝ}, Relation.TransGen (IsFutureCausalStep g X U) p q → f p < f q := by
    intro q hq
    induction hq with
    | single hstep => exact hf.lt_of_isFutureCausalStep hstep
    | tail _ hstep ih => exact ih.trans (hf.lt_of_isFutureCausalStep hstep)
  exact lt_irrefl _ (this hp)

/-- The existence of a time function implies that the spacetime is chronological. -/
lemma isChronologicalSpacetimeOn (hf : IsTimeFunctionOn g X U f) :
    IsChronologicalSpacetimeOn g X U :=
  hf.isCausalSpacetimeOn.isChronologicalSpacetimeOn

end IsTimeFunctionOn

/-- A closed future-directed causal curve: a future-directed causal curve with `γ b = γ a`. -/
def IsClosedFutureCausalCurve (g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ)
    (X : (Fin 4 → ℝ) → Fin 4 → ℝ) (U : Set (Fin 4 → ℝ)) (γ : ℝ → Fin 4 → ℝ) (a b : ℝ) :
    Prop :=
  IsFutureCausalCurveOn g X U γ a b ∧ γ b = γ a

/-- There is no closed future-directed causal curve when a time function exists. -/
lemma not_isClosedFutureCausalCurve_of_isTimeFunctionOn {f : (Fin 4 → ℝ) → ℝ}
    (hf : IsTimeFunctionOn g X U f) : ¬ IsClosedFutureCausalCurve g X U γ a b := fun h =>
  hf.isCausalSpacetimeOn (γ a) (Relation.TransGen.single ⟨γ, a, b, h.1, rfl, h.2⟩)

/-!

## C. Minkowski space is causal and chronological

-/

/-- A future-directed causal vector for the Minkowski metric has positive time component, when the
time orientation `X` is timelike with positive time component. -/
lemma time_pos_of_future_causal_minkowskiField {x X v : Fin 4 → ℝ}
    (hX : IsTimelike (Matrix.toBilin' (minkowskiField x)) X) (hX0 : 0 < X 0)
    (hv : IsCausal (Matrix.toBilin' (minkowskiField x)) v)
    (hlt : Matrix.toBilin' (minkowskiField x) X v < 0) : 0 < v 0 := by
  by_contra hneg
  rw [not_lt] at hneg
  have hX' := hX
  have hv' := hv.1
  simp only [IsTimelike, minkowskiField_bilin] at hX'
  simp only [minkowskiField_bilin] at hv' hlt
  have hcs : (X 1 * v 1 + X 2 * v 2 + X 3 * v 3) ^ 2 ≤
      (X 1 ^ 2 + X 2 ^ 2 + X 3 ^ 2) * (v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2) := by
    nlinarith [sq_nonneg (X 1 * v 2 - X 2 * v 1), sq_nonneg (X 1 * v 3 - X 3 * v 1),
      sq_nonneg (X 2 * v 3 - X 3 * v 2)]
  have hw : 0 ≤ -(v 0) := by linarith
  have hsum : 0 ≤ X 1 ^ 2 + X 2 ^ 2 + X 3 ^ 2 := by positivity
  have hvs : v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2 ≤ (v 0) ^ 2 := by nlinarith
  have h1 : X 0 * -(v 0) < -(X 1 * v 1 + X 2 * v 2 + X 3 * v 3) := by nlinarith
  have h2 : (X 0 * -(v 0)) ^ 2 < (X 1 * v 1 + X 2 * v 2 + X 3 * v 3) ^ 2 := by
    have h0 : 0 ≤ X 0 * -(v 0) := mul_nonneg hX0.le hw
    nlinarith
  have h3 : (X 1 ^ 2 + X 2 ^ 2 + X 3 ^ 2) * (v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2) ≤
      (X 0 * -(v 0)) ^ 2 := by
    calc _ ≤ (X 1 ^ 2 + X 2 ^ 2 + X 3 ^ 2) * (v 0) ^ 2 := mul_le_mul_of_nonneg_left hvs hsum
      _ ≤ (X 0) ^ 2 * (v 0) ^ 2 := by nlinarith [sq_nonneg (v 0)]
      _ = _ := by ring
  linarith

/-- The time coordinate `x ↦ x 0` is a time function on Minkowski space, for any time orientation
`X` with positive time component. -/
lemma isTimeFunctionOn_minkowskiField (hX : IsTimeOrientationOn minkowskiField U X)
    (hX0 : ∀ x ∈ U, 0 < X x 0) : IsTimeFunctionOn minkowskiField X U (fun x => x 0) where
  continuousOn := (continuous_apply 0).continuousOn
  strictMonoOn γ a b h := by
    obtain ⟨⟨hab, hcd, hU, hcausal⟩, hfut⟩ := h
    refine strictMonoOn_of_deriv_pos (convex_Icc a b)
      ((continuous_apply 0).comp_continuousOn hcd.continuousOn) fun c hc => ?_
    rw [interior_Icc] at hc
    have hnhds : Icc a b ∈ nhds c := Icc_mem_nhds hc.1 hc.2
    have hdiff : DifferentiableAt ℝ γ c := (hcd.contDiffAt hnhds).differentiableAt (by simp)
    have hder : derivWithin γ (Icc a b) c = deriv γ c := derivWithin_of_mem_nhds hnhds
    have hcomp : HasDerivAt (fun s => γ s 0) (deriv γ c 0) c :=
      hasDerivAt_pi.mp hdiff.hasDerivAt 0
    have hcm : c ∈ Icc a b := Ioo_subset_Icc_self hc
    have hγU : γ c ∈ U := hU c hcm
    rw [hcomp.deriv]
    refine time_pos_of_future_causal_minkowskiField (hX.isTimelike _ hγU) (hX0 _ hγU) ?_ ?_
    · exact hder ▸ hcausal c hcm
    · exact hder ▸ hfut c hcm

/-- Minkowski space is causal: it has no closed piecewise `C¹` future-directed causal curve. -/
lemma isCausalSpacetimeOn_minkowskiField (hX : IsTimeOrientationOn minkowskiField U X)
    (hX0 : ∀ x ∈ U, 0 < X x 0) : IsCausalSpacetimeOn minkowskiField X U :=
  (isTimeFunctionOn_minkowskiField hX hX0).isCausalSpacetimeOn

/-- Minkowski space is chronological. -/
lemma isChronologicalSpacetimeOn_minkowskiField (hX : IsTimeOrientationOn minkowskiField U X)
    (hX0 : ∀ x ∈ U, 0 < X x 0) : IsChronologicalSpacetimeOn minkowskiField X U :=
  (isCausalSpacetimeOn_minkowskiField hX hX0).isChronologicalSpacetimeOn

/-- The chronology violating set of Minkowski space is empty. -/
lemma chronologyViolatingSet_minkowskiField (hX : IsTimeOrientationOn minkowskiField U X)
    (hX0 : ∀ x ∈ U, 0 < X x 0) : chronologyViolatingSet minkowskiField X U = ∅ :=
  isChronologicalSpacetimeOn_iff.1 (isChronologicalSpacetimeOn_minkowskiField hX hX0)

end GeneralRelativity
