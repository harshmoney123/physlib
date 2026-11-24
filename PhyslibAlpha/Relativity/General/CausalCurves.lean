/-
Copyright (c) 2026 Harsha Vankayalapati. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harsha Vankayalapati
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.LocalExtr.Rolle
public import PhyslibAlpha.Relativity.General.CoordinateMetric

/-!

# Causal curves and closed timelike curves

Timelike and causal curves in a coordinate spacetime, and closed timelike curves.

## i. Overview

In a coordinate chart a curve is a map `γ : ℝ → Fin 4 → ℝ`, restricted to a compact interval
`[a, b]`. It is a timelike (causal) curve for a metric field `g` on an open set `U` if it is `C¹`,
stays in `U`, and its tangent vector `γ'(t)` is timelike (causal) for `g (γ t)` at every parameter.

A closed curve in the spacetime obtained from `U` by identifying points that differ by a period
`τ` (for example the flat cylinder, Minkowski space with `t ~ t + T`) is a curve in the covering
space whose endpoints differ by `τ`. We call such a curve a timelike (causal) loop modulo `τ`
(`IsTimelikeLoopMod`). A closed timelike curve in the spacetime `U` itself is the case `τ = 0`
(`IsClosedTimelikeCurve`). A timelike loop has a tangent of constant time orientation, so it need
not be oriented separately.

For Minkowski space, the time coordinate is strictly monotone along any causal curve, so there is
no closed causal curve (`not_isClosedCausalCurve_minkowskiField`), and more generally no causal
loop modulo a purely spatial period. On the flat cylinder, the curve `t ↦ (t, 0, 0, 0)`, `0 ≤ t ≤ T`
is a closed timelike curve (`exists_isTimelikeLoopMod_cylinder`).

## ii. Key results

- `IsTimelikeCurveOn`, `IsCausalCurveOn` : timelike and causal curves.
- `IsTimelikeLoopMod`, `IsClosedTimelikeCurve` : closed timelike curves, possibly modulo a period.
- `IsTimelikeCurveOn.isCausalCurveOn` : a timelike curve is causal.
- `IsTimelikeCurveOn.mono`, `IsCausalCurveOn.mono` : restriction to a subinterval.
- `time_ne_of_isCausalCurveOn_minkowskiField` : time is strictly monotone along causal curves
  in Minkowski space.
- `not_isClosedCausalCurve_minkowskiField` : Minkowski space has no closed causal curve, hence
  no closed timelike curve.
- `exists_isTimelikeLoopMod_cylinder` : the flat cylinder has a closed timelike curve.

## iii. Table of contents

- A. Causal curves
- B. Closed timelike curves
- C. Minkowski space has no closed causal curves
- D. The flat cylinder has a closed timelike curve

## iv. References

- S. W. Hawking and G. F. R. Ellis, *The Large Scale Structure of Space-Time*, Chapter 6.

-/

@[expose] public section

noncomputable section

namespace GeneralRelativity

open Set

/-!

## A. Causal curves

-/

/-- A timelike curve `γ` on `[a, b]` for the metric field `g` on `U`: `a < b`, `γ` is `C¹` and
stays in `U`, and its tangent vector is timelike for `g (γ t)` at every `t ∈ [a, b]`. -/
def IsTimelikeCurveOn (g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ) (U : Set (Fin 4 → ℝ))
    (γ : ℝ → Fin 4 → ℝ) (a b : ℝ) : Prop :=
  a < b ∧ ContDiffOn ℝ 1 γ (Icc a b) ∧ (∀ t ∈ Icc a b, γ t ∈ U) ∧
    ∀ t ∈ Icc a b, IsTimelike (Matrix.toBilin' (g (γ t))) (derivWithin γ (Icc a b) t)

/-- A causal curve `γ` on `[a, b]` for the metric field `g` on `U`: as for `IsTimelikeCurveOn`,
but the tangent vector is only required to be causal (timelike or null, and nonzero). -/
def IsCausalCurveOn (g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ) (U : Set (Fin 4 → ℝ))
    (γ : ℝ → Fin 4 → ℝ) (a b : ℝ) : Prop :=
  a < b ∧ ContDiffOn ℝ 1 γ (Icc a b) ∧ (∀ t ∈ Icc a b, γ t ∈ U) ∧
    ∀ t ∈ Icc a b, IsCausal (Matrix.toBilin' (g (γ t))) (derivWithin γ (Icc a b) t)

/-- A timelike curve is a causal curve. -/
lemma IsTimelikeCurveOn.isCausalCurveOn {g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
    {U : Set (Fin 4 → ℝ)} {γ : ℝ → Fin 4 → ℝ} {a b : ℝ} (h : IsTimelikeCurveOn g U γ a b) :
    IsCausalCurveOn g U γ a b :=
  ⟨h.1, h.2.1, h.2.2.1, fun t ht => (h.2.2.2 t ht).isCausal⟩

/-- Restricting `γ` to a subinterval does not change its derivative within the interval. -/
lemma derivWithin_Icc_of_subset {γ : ℝ → Fin 4 → ℝ} {a b c d t : ℝ}
    (hγ : ContDiffOn ℝ 1 γ (Icc a b)) (hac : a ≤ c) (hdb : d ≤ b) (hcd : c < d)
    (ht : t ∈ Icc c d) : derivWithin γ (Icc c d) t = derivWithin γ (Icc a b) t := by
  have hsub : Icc c d ⊆ Icc a b := Icc_subset_Icc hac hdb
  have hdiff : DifferentiableWithinAt ℝ γ (Icc a b) t :=
    (hγ.differentiableOn one_ne_zero) t (hsub ht)
  exact (hdiff.hasDerivWithinAt.mono hsub).derivWithin (uniqueDiffOn_Icc hcd t ht)

/-- The restriction of a timelike curve to a subinterval is a timelike curve. -/
lemma IsTimelikeCurveOn.mono {g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
    {U : Set (Fin 4 → ℝ)} {γ : ℝ → Fin 4 → ℝ} {a b c d : ℝ} (h : IsTimelikeCurveOn g U γ a b)
    (hac : a ≤ c) (hdb : d ≤ b) (hcd : c < d) : IsTimelikeCurveOn g U γ c d :=
  ⟨hcd, h.2.1.mono (Icc_subset_Icc hac hdb), fun t ht => h.2.2.1 t (Icc_subset_Icc hac hdb ht),
    fun t ht => by
      rw [derivWithin_Icc_of_subset h.2.1 hac hdb hcd ht]
      exact h.2.2.2 t (Icc_subset_Icc hac hdb ht)⟩

/-- The restriction of a causal curve to a subinterval is a causal curve. -/
lemma IsCausalCurveOn.mono {g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
    {U : Set (Fin 4 → ℝ)} {γ : ℝ → Fin 4 → ℝ} {a b c d : ℝ} (h : IsCausalCurveOn g U γ a b)
    (hac : a ≤ c) (hdb : d ≤ b) (hcd : c < d) : IsCausalCurveOn g U γ c d :=
  ⟨hcd, h.2.1.mono (Icc_subset_Icc hac hdb), fun t ht => h.2.2.1 t (Icc_subset_Icc hac hdb ht),
    fun t ht => by
      rw [derivWithin_Icc_of_subset h.2.1 hac hdb hcd ht]
      exact h.2.2.2 t (Icc_subset_Icc hac hdb ht)⟩

/-!

## B. Closed timelike curves

-/

/-- A timelike loop modulo the period `τ`: a timelike curve in the covering space whose endpoints
differ by `τ`. It is a closed timelike curve of the spacetime obtained by identifying points
that differ by `τ`. -/
def IsTimelikeLoopMod (g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ) (U : Set (Fin 4 → ℝ))
    (τ : Fin 4 → ℝ) (γ : ℝ → Fin 4 → ℝ) (a b : ℝ) : Prop :=
  IsTimelikeCurveOn g U γ a b ∧ γ b = γ a + τ

/-- A causal loop modulo the period `τ`. -/
def IsCausalLoopMod (g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ) (U : Set (Fin 4 → ℝ))
    (τ : Fin 4 → ℝ) (γ : ℝ → Fin 4 → ℝ) (a b : ℝ) : Prop :=
  IsCausalCurveOn g U γ a b ∧ γ b = γ a + τ

/-- A closed timelike curve: a timelike curve with `γ b = γ a`. -/
def IsClosedTimelikeCurve (g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ) (U : Set (Fin 4 → ℝ))
    (γ : ℝ → Fin 4 → ℝ) (a b : ℝ) : Prop :=
  IsTimelikeCurveOn g U γ a b ∧ γ b = γ a

/-- A closed causal curve: a causal curve with `γ b = γ a`. -/
def IsClosedCausalCurve (g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ) (U : Set (Fin 4 → ℝ))
    (γ : ℝ → Fin 4 → ℝ) (a b : ℝ) : Prop :=
  IsCausalCurveOn g U γ a b ∧ γ b = γ a

lemma isClosedTimelikeCurve_iff_loopMod_zero {g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
    {U : Set (Fin 4 → ℝ)} {γ : ℝ → Fin 4 → ℝ} {a b : ℝ} :
    IsClosedTimelikeCurve g U γ a b ↔ IsTimelikeLoopMod g U 0 γ a b := by
  simp [IsClosedTimelikeCurve, IsTimelikeLoopMod]

/-- A closed timelike curve is a closed causal curve. -/
lemma IsClosedTimelikeCurve.isClosedCausalCurve {g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
    {U : Set (Fin 4 → ℝ)} {γ : ℝ → Fin 4 → ℝ} {a b : ℝ} (h : IsClosedTimelikeCurve g U γ a b) :
    IsClosedCausalCurve g U γ a b :=
  ⟨h.1.isCausalCurveOn, h.2⟩

/-!

## C. Minkowski space has no closed causal curves

-/

/-- A causal vector of the Minkowski metric has non-zero time component. -/
private lemma time_component_ne_zero_of_isCausal {v : Fin 4 → ℝ} (x : Fin 4 → ℝ)
    (hv : IsCausal (Matrix.toBilin' (minkowskiField x)) v) : v 0 ≠ 0 := by
  intro h0
  have h := hv.1
  rw [minkowskiField_bilin, h0] at h
  refine hv.2 (funext fun i => ?_)
  have h1 := sq_nonneg (v 1)
  have h2 := sq_nonneg (v 2)
  have h3 := sq_nonneg (v 3)
  have e1 : v 1 = 0 := by nlinarith
  have e2 : v 2 = 0 := by nlinarith
  have e3 : v 3 = 0 := by nlinarith
  fin_cases i <;> simp [h0, e1, e2, e3]

/-- Along a causal curve in Minkowski space the time coordinate takes different values at the
endpoints. -/
lemma time_ne_of_isCausalCurveOn_minkowskiField {U : Set (Fin 4 → ℝ)} {γ : ℝ → Fin 4 → ℝ}
    {a b : ℝ} (h : IsCausalCurveOn minkowskiField U γ a b) : γ a 0 ≠ γ b 0 := by
  obtain ⟨hab, hcd, -, hcausal⟩ := h
  intro heq
  obtain ⟨c, hc, hdc⟩ := exists_deriv_eq_zero (f := fun s => γ s 0) hab
    ((continuous_apply 0).comp_continuousOn hcd.continuousOn) heq
  have hnhds : Icc a b ∈ nhds c := Icc_mem_nhds hc.1 hc.2
  have hdiff : DifferentiableAt ℝ γ c :=
    ((hcd.contDiffAt hnhds).differentiableAt (by simp))
  have hder : derivWithin γ (Icc a b) c = deriv γ c := derivWithin_of_mem_nhds hnhds
  have hcomp : HasDerivAt (fun s => γ s 0) (deriv γ c 0) c :=
    hasDerivAt_pi.mp hdiff.hasDerivAt 0
  have hzero : deriv γ c 0 = 0 := hcomp.deriv.symm.trans hdc
  have := time_component_ne_zero_of_isCausal (γ c) (hder ▸ hcausal c (Ioo_subset_Icc_self hc))
  exact this hzero

/-- Minkowski space has no closed causal curve. -/
lemma not_isClosedCausalCurve_minkowskiField {U : Set (Fin 4 → ℝ)} {γ : ℝ → Fin 4 → ℝ}
    {a b : ℝ} : ¬ IsClosedCausalCurve minkowskiField U γ a b :=
  fun h => time_ne_of_isCausalCurveOn_minkowskiField h.1 (by rw [h.2])

/-- Minkowski space has no closed timelike curve. -/
lemma not_isClosedTimelikeCurve_minkowskiField {U : Set (Fin 4 → ℝ)} {γ : ℝ → Fin 4 → ℝ}
    {a b : ℝ} : ¬ IsClosedTimelikeCurve minkowskiField U γ a b :=
  fun h => not_isClosedCausalCurve_minkowskiField h.isClosedCausalCurve

/-- There is no causal loop in Minkowski space modulo a purely spatial period. -/
lemma not_isCausalLoopMod_of_time_eq_zero {U : Set (Fin 4 → ℝ)} {τ : Fin 4 → ℝ} (hτ : τ 0 = 0)
    {γ : ℝ → Fin 4 → ℝ} {a b : ℝ} : ¬ IsCausalLoopMod minkowskiField U τ γ a b :=
  fun h => time_ne_of_isCausalCurveOn_minkowskiField h.1 (by simp [h.2, hτ])

/-!

## D. The flat cylinder has a closed timelike curve

-/

/-- The period of the flat cylinder: Minkowski space with `t ~ t + T`. -/
def cylinderPeriod (T : ℝ) : Fin 4 → ℝ := Pi.single 0 T

/-- The curve `t ↦ (t, 0, 0, 0)` winding once around the flat cylinder, as a timelike loop
modulo `cylinderPeriod T` in the covering Minkowski space. -/
lemma isTimelikeLoopMod_cylinder {T : ℝ} (hT : 0 < T) :
    IsTimelikeLoopMod minkowskiField Set.univ (cylinderPeriod T) (fun t => Pi.single 0 t) 0 T := by
  have hd : ∀ t : ℝ, HasDerivAt (fun s : ℝ => (Pi.single 0 s : Fin 4 → ℝ)) (Pi.single 0 1) t :=
    fun t => by
      refine hasDerivAt_pi.mpr fun i => ?_
      by_cases hi : i = 0
      · subst hi; simpa using hasDerivAt_id' t
      · simpa [Pi.single_apply, hi] using hasDerivAt_const t (0 : ℝ)
  refine ⟨⟨hT, ?_, fun _ _ => mem_univ _, fun t ht => ?_⟩, by simp [cylinderPeriod]⟩
  · exact (contDiff_pi.mpr fun i => by
      by_cases hi : i = 0
      · subst hi; exact contDiff_id
      · simpa [Pi.single_apply, hi] using contDiff_const).contDiffOn
  · have hu : UniqueDiffWithinAt ℝ (Icc 0 T) t := uniqueDiffOn_Icc hT t ht
    rw [((hd t).hasDerivWithinAt).derivWithin hu]
    simp only [IsTimelike, minkowskiField_bilin]
    simp

/-- The flat cylinder has a closed timelike curve: a timelike loop modulo its period. -/
lemma exists_isTimelikeLoopMod_cylinder {T : ℝ} (hT : 0 < T) :
    ∃ (γ : ℝ → Fin 4 → ℝ) (a b : ℝ),
      IsTimelikeLoopMod minkowskiField Set.univ (cylinderPeriod T) γ a b :=
  ⟨_, 0, T, isTimelikeLoopMod_cylinder hT⟩

end GeneralRelativity
