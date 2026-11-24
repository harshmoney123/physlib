/-
Copyright (c) 2026 Harsha Vankayalapati. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harsha Vankayalapati
-/
module

public import Mathlib.Analysis.SpecialFunctions.Arsinh
public import PhyslibAlpha.Relativity.General.CausalCurves
public import PhyslibAlpha.Relativity.General.Godel.Metric

/-!

# Closed timelike curves in the Gödel universe

Beyond the critical radius `r_c = ln (1 + √2)` the circles around the axis are closed timelike
curves.

## i. Overview

The tangent vector `∂_φ` of the circle `φ ↦ (t₀, r₀, φ, z₀)` has norm
`g_{φφ} = sinh² r₀ (1 - sinh² r₀)`, which is negative exactly when `sinh r₀ > 1`, that is
`r₀ > r_c = arsinh 1 = ln (1 + √2)`. In the cylindrical coordinates `φ` is periodic with period
`2 π`, so the circle is a timelike loop modulo the period `(0, 0, 2 π, 0)`
(`isTimelikeLoopMod_godelCircle`): a closed timelike curve of Gödel's universe. Gödel's universe
therefore violates causality: it is the first spacetime in this library in which a particle can
travel into its own past.

## ii. Key results

- `godelCriticalRadius` : the critical radius `r_c = arsinh 1`, equal to `ln (1 + √2)`
  (`godelCriticalRadius_eq`).
- `godelCircle` : the circle of constant `t`, `r`, `z`.
- `isTimelikeLoopMod_godelCircle` : the circle beyond the critical radius is a closed timelike
  curve.
- `exists_isTimelikeLoopMod_godel` : the Gödel universe has a closed timelike curve.

## iii. Table of contents

- A. The critical radius
- B. The circles of constant radius
- C. Closed timelike curves

## iv. References

- K. Gödel, *An example of a new type of cosmological solutions of Einstein's field equations of
  gravitation*, Rev. Mod. Phys. 21, 447 (1949).

-/

@[expose] public section

noncomputable section

namespace GeneralRelativity

open Real Set

/-!

## A. The critical radius

-/

/-- The critical radius `r_c = arsinh 1` of the Gödel universe, beyond which the circles around
the axis are timelike. -/
def godelCriticalRadius : ℝ := arsinh 1

/-- The critical radius is `ln (1 + √2)`. -/
lemma godelCriticalRadius_eq : godelCriticalRadius = log (1 + √2) := by
  simp only [godelCriticalRadius, arsinh]
  norm_num

/-- The critical radius is positive. -/
lemma godelCriticalRadius_pos : 0 < godelCriticalRadius := arsinh_pos_iff.2 one_pos

/-- Beyond the critical radius `sinh r > 1`. -/
lemma one_lt_sinh_of_godelCriticalRadius_lt {r : ℝ} (h : godelCriticalRadius < r) :
    1 < sinh r := by
  have := sinh_lt_sinh.2 h
  rwa [godelCriticalRadius, sinh_arsinh] at this

/-!

## B. The circles of constant radius

-/

/-- The circle `φ ↦ (t₀, r₀, φ, z₀)` of constant `t`, `r` and `z`. -/
def godelCircle (t₀ r₀ z₀ : ℝ) (s : ℝ) : Fin 4 → ℝ := ![t₀, r₀, s, z₀]

/-- The period `(0, 0, 2 π, 0)` of the angular coordinate. -/
def godelPeriod : Fin 4 → ℝ := Pi.single 2 (2 * π)

/-- The tangent vector of the circle is `∂_φ`. -/
lemma hasDerivAt_godelCircle (t₀ r₀ z₀ s : ℝ) :
    HasDerivAt (godelCircle t₀ r₀ z₀) ![0, 0, 1, 0] s := by
  refine hasDerivAt_pi.2 fun i => ?_
  fin_cases i
  · simpa [godelCircle] using hasDerivAt_const s t₀
  · simpa [godelCircle] using hasDerivAt_const s r₀
  · simpa [godelCircle] using hasDerivAt_id' s
  · simpa [godelCircle] using hasDerivAt_const s z₀

/-!

## C. Closed timelike curves

-/

/-- Beyond the critical radius the circle of constant `t`, `r`, `z` is a timelike loop modulo
the angular period. -/
lemma isTimelikeLoopMod_godelCircle {t₀ r₀ z₀ : ℝ} (h : godelCriticalRadius < r₀) :
    IsTimelikeLoopMod godelMetric godelDomain godelPeriod (godelCircle t₀ r₀ z₀) 0 (2 * π) := by
  have hr : 0 < r₀ := godelCriticalRadius_pos.trans h
  have h1 := one_lt_sinh_of_godelCriticalRadius_lt h
  refine ⟨⟨by positivity, ?_, fun s _ => ?_, fun s hs => ?_⟩, ?_⟩
  · exact (contDiff_pi.2 fun i => by
      fin_cases i <;> simp [godelCircle] <;> fun_prop).contDiffOn
  · simpa [godelDomain, godelCircle] using hr
  · have hu : UniqueDiffWithinAt ℝ (Icc 0 (2 * π)) s := uniqueDiffOn_Icc (by positivity) s hs
    rw [(hasDerivAt_godelCircle t₀ r₀ z₀ s).hasDerivWithinAt.derivWithin hu]
    simp only [IsTimelike, godelMetric_bilin]
    simp [godelCircle]
    nlinarith [sq_nonneg (sinh r₀), mul_pos (by positivity : (0 : ℝ) < sinh r₀ ^ 2)
      (by nlinarith : (0 : ℝ) < sinh r₀ ^ 2 - 1)]
  · funext i
    fin_cases i <;> simp [godelCircle, godelPeriod]

/-- The Gödel universe has a closed timelike curve: Gödel's universe violates causality. -/
theorem exists_isTimelikeLoopMod_godel :
    ∃ (γ : ℝ → Fin 4 → ℝ) (a b : ℝ),
      IsTimelikeLoopMod godelMetric godelDomain godelPeriod γ a b :=
  ⟨godelCircle 0 (godelCriticalRadius + 1) 0, 0, 2 * π,
    isTimelikeLoopMod_godelCircle (by linarith)⟩

end GeneralRelativity
