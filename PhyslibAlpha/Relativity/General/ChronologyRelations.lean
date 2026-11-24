/-
Copyright (c) 2026 Harsha Vankayalapati. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harsha Vankayalapati
-/
module

public import PhyslibAlpha.Relativity.General.CausalCurves
public import Mathlib.Logic.Relation

/-!

# Chronological and causal relations

The chronological future `I⁺(p)`, the causal future `J⁺(p)` and the chronology violating set.

## i. Overview

A time orientation on a coordinate spacetime `(U, g)` is a vector field `X` which is timelike for
`g` on `U` (`IsTimeOrientationOn`). A curve is future-directed if its tangent `γ'(t)` satisfies
`g (X (γ t)) (γ' t) < 0` at every parameter.

Following Hawking and Ellis, `I⁺(p)` consists of the points which can be reached from `p` by a
piecewise `C¹` future-directed timelike curve. A piecewise `C¹` curve is a finite concatenation of
`C¹` segments, so we define the relation `IsFutureTimelikeStep` for a single `C¹` segment and let
`I⁺(p)` be its transitive closure. Likewise `J⁺(p)` is the reflexive transitive closure of the
relation for future-directed causal segments, so that `p ∈ J⁺(p)`. The chronology violating set
is the set of points `p` with `p ∈ I⁺(p)`.

## ii. Key results

- `IsFutureTimelikeCurveOn`, `IsFutureCausalCurveOn` : future-directed timelike and causal curves.
- `chronologicalFuture`, `causalFuture` : the sets `I⁺(p)` and `J⁺(p)`.
- `chronologyViolatingSet` : the set of points `p` with `p ∈ I⁺(p)`.
- `chronologicalFuture_trans` : `I⁺` is transitive.
- `chronologicalFuture_subset_causalFuture` : `I⁺(p) ⊆ J⁺(p)`.
- `mem_chronologicalFuture_of_isClosedFutureTimelikeCurve` : a point on a closed future-directed
  timelike curve lies in its own chronological future, so chronology is violated there.

## iii. Table of contents

- A. Future-directed curves
- B. The relations `I⁺` and `J⁺`
- C. Closed timelike curves violate chronology

## iv. References

- S. W. Hawking and G. F. R. Ellis, *The Large Scale Structure of Space-Time*, Chapter 6.
- B. O'Neill, *Semi-Riemannian Geometry*, Chapter 14.

-/

@[expose] public section

noncomputable section

namespace GeneralRelativity

open Set

/-!

## A. Future-directed curves

-/

/-- A time orientation on the coordinate spacetime `(U, g)`: a continuous vector field `X` on `U`
which is timelike for `g`. -/
structure IsTimeOrientationOn (g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ) (U : Set (Fin 4 → ℝ))
    (X : (Fin 4 → ℝ) → Fin 4 → ℝ) : Prop where
  /-- The vector field is continuous. -/
  continuousOn : ContinuousOn X U
  /-- The vector field is timelike. -/
  isTimelike : ∀ x ∈ U, IsTimelike (Matrix.toBilin' (g x)) (X x)

/-- A future-directed timelike curve on `[a, b]`: a timelike curve whose tangent `v` satisfies
`g (X (γ t)) v < 0`. -/
def IsFutureTimelikeCurveOn (g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ) (X : (Fin 4 → ℝ) → Fin 4 → ℝ)
    (U : Set (Fin 4 → ℝ)) (γ : ℝ → Fin 4 → ℝ) (a b : ℝ) : Prop :=
  IsTimelikeCurveOn g U γ a b ∧
    ∀ t ∈ Icc a b, Matrix.toBilin' (g (γ t)) (X (γ t)) (derivWithin γ (Icc a b) t) < 0

/-- A future-directed causal curve on `[a, b]`: a causal curve whose tangent `v` satisfies
`g (X (γ t)) v < 0`. -/
def IsFutureCausalCurveOn (g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ) (X : (Fin 4 → ℝ) → Fin 4 → ℝ)
    (U : Set (Fin 4 → ℝ)) (γ : ℝ → Fin 4 → ℝ) (a b : ℝ) : Prop :=
  IsCausalCurveOn g U γ a b ∧
    ∀ t ∈ Icc a b, Matrix.toBilin' (g (γ t)) (X (γ t)) (derivWithin γ (Icc a b) t) < 0

variable {g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ} {X : (Fin 4 → ℝ) → Fin 4 → ℝ}
  {U : Set (Fin 4 → ℝ)} {γ : ℝ → Fin 4 → ℝ} {a b c d : ℝ}

/-- A future-directed timelike curve is a future-directed causal curve. -/
lemma IsFutureTimelikeCurveOn.isFutureCausalCurveOn (h : IsFutureTimelikeCurveOn g X U γ a b) :
    IsFutureCausalCurveOn g X U γ a b :=
  ⟨h.1.isCausalCurveOn, h.2⟩

/-- The restriction of a future-directed timelike curve to a subinterval is again one. -/
lemma IsFutureTimelikeCurveOn.mono (h : IsFutureTimelikeCurveOn g X U γ a b)
    (hac : a ≤ c) (hdb : d ≤ b) (hcd : c < d) : IsFutureTimelikeCurveOn g X U γ c d :=
  ⟨h.1.mono hac hdb hcd, fun t ht => by
    rw [derivWithin_Icc_of_subset h.1.2.1 hac hdb hcd ht]
    exact h.2 t (Icc_subset_Icc hac hdb ht)⟩

/-!

## B. The relations `I⁺` and `J⁺`

-/

/-- `q` is reached from `p` by one `C¹` future-directed timelike segment. -/
def IsFutureTimelikeStep (g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ)
    (X : (Fin 4 → ℝ) → Fin 4 → ℝ) (U : Set (Fin 4 → ℝ)) (p q : Fin 4 → ℝ) : Prop :=
  ∃ (γ : ℝ → Fin 4 → ℝ) (a b : ℝ), IsFutureTimelikeCurveOn g X U γ a b ∧ γ a = p ∧ γ b = q

/-- `q` is reached from `p` by one `C¹` future-directed causal segment. -/
def IsFutureCausalStep (g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ)
    (X : (Fin 4 → ℝ) → Fin 4 → ℝ) (U : Set (Fin 4 → ℝ)) (p q : Fin 4 → ℝ) : Prop :=
  ∃ (γ : ℝ → Fin 4 → ℝ) (a b : ℝ), IsFutureCausalCurveOn g X U γ a b ∧ γ a = p ∧ γ b = q

/-- The chronological future `I⁺(p)`: the points reached from `p` by a piecewise `C¹`
future-directed timelike curve, that is by a finite chain of `C¹` timelike segments. -/
def chronologicalFuture (g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ)
    (X : (Fin 4 → ℝ) → Fin 4 → ℝ) (U : Set (Fin 4 → ℝ)) (p : Fin 4 → ℝ) : Set (Fin 4 → ℝ) :=
  {q | Relation.TransGen (IsFutureTimelikeStep g X U) p q}

/-- The causal future `J⁺(p)`: the point `p` together with the points reached from `p` by a
piecewise `C¹` future-directed causal curve. -/
def causalFuture (g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ)
    (X : (Fin 4 → ℝ) → Fin 4 → ℝ) (U : Set (Fin 4 → ℝ)) (p : Fin 4 → ℝ) : Set (Fin 4 → ℝ) :=
  {q | Relation.ReflTransGen (IsFutureCausalStep g X U) p q}

/-- The chronology violating set: the points `p` with `p ∈ I⁺(p)`. -/
def chronologyViolatingSet (g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ)
    (X : (Fin 4 → ℝ) → Fin 4 → ℝ) (U : Set (Fin 4 → ℝ)) : Set (Fin 4 → ℝ) :=
  {p | p ∈ chronologicalFuture g X U p}

/-- A point reached by one future-directed timelike segment lies in the chronological future. -/
lemma IsFutureTimelikeStep.mem_chronologicalFuture {p q : Fin 4 → ℝ}
    (h : IsFutureTimelikeStep g X U p q) : q ∈ chronologicalFuture g X U p :=
  Relation.TransGen.single h

/-- `I⁺` is transitive: if `q ∈ I⁺(p)` and `r ∈ I⁺(q)` then `r ∈ I⁺(p)`. -/
lemma chronologicalFuture_trans {p q r : Fin 4 → ℝ} (hq : q ∈ chronologicalFuture g X U p)
    (hr : r ∈ chronologicalFuture g X U q) : r ∈ chronologicalFuture g X U p :=
  Relation.TransGen.trans hq hr

/-- `J⁺` is transitive. -/
lemma causalFuture_trans {p q r : Fin 4 → ℝ} (hq : q ∈ causalFuture g X U p)
    (hr : r ∈ causalFuture g X U q) : r ∈ causalFuture g X U p :=
  Relation.ReflTransGen.trans hq hr

/-- A point lies in its own causal future. -/
lemma self_mem_causalFuture (p : Fin 4 → ℝ) : p ∈ causalFuture g X U p :=
  Relation.ReflTransGen.refl

/-- The chronological future is contained in the causal future: `I⁺(p) ⊆ J⁺(p)`. -/
lemma chronologicalFuture_subset_causalFuture (p : Fin 4 → ℝ) :
    chronologicalFuture g X U p ⊆ causalFuture g X U p := fun _ hq =>
  (Relation.TransGen.mono (fun _ _ ⟨γ, a, b, h, ha, hb⟩ =>
    ⟨γ, a, b, h.isFutureCausalCurveOn, ha, hb⟩) _ _ hq).to_reflTransGen

/-!

## C. Closed timelike curves violate chronology

-/

/-- A closed future-directed timelike curve: a future-directed timelike curve with `γ b = γ a`. -/
def IsClosedFutureTimelikeCurve (g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ)
    (X : (Fin 4 → ℝ) → Fin 4 → ℝ) (U : Set (Fin 4 → ℝ)) (γ : ℝ → Fin 4 → ℝ) (a b : ℝ) :
    Prop :=
  IsFutureTimelikeCurveOn g X U γ a b ∧ γ b = γ a

/-- A point on a closed future-directed timelike curve lies in its own chronological future. -/
lemma mem_chronologicalFuture_of_isClosedFutureTimelikeCurve
    (h : IsClosedFutureTimelikeCurve g X U γ a b) {t : ℝ} (ht : t ∈ Icc a b) :
    γ t ∈ chronologicalFuture g X U (γ t) := by
  obtain ⟨hcurve, hclosed⟩ := h
  have hab : a < b := hcurve.1.1
  have hstep : IsFutureTimelikeStep g X U (γ a) (γ a) := ⟨γ, a, b, hcurve, rfl, hclosed⟩
  by_cases hta : t = a
  · rw [hta]
    exact hstep.mem_chronologicalFuture
  by_cases htb : t = b
  · rw [htb, hclosed]
    exact hstep.mem_chronologicalFuture
  have hat : a < t := lt_of_le_of_ne ht.1 (Ne.symm hta)
  have htb : t < b := lt_of_le_of_ne ht.2 htb
  have h1 : IsFutureTimelikeStep g X U (γ t) (γ a) :=
    ⟨γ, t, b, hcurve.mono ht.1 le_rfl htb, rfl, hclosed⟩
  have h2 : IsFutureTimelikeStep g X U (γ a) (γ t) :=
    ⟨γ, a, t, hcurve.mono le_rfl ht.2 hat, rfl, rfl⟩
  exact Relation.TransGen.head h1 (Relation.TransGen.single h2)

/-- A point on a closed future-directed timelike curve is chronology violating. -/
lemma mem_chronologyViolatingSet_of_isClosedFutureTimelikeCurve
    (h : IsClosedFutureTimelikeCurve g X U γ a b) {t : ℝ} (ht : t ∈ Icc a b) :
    γ t ∈ chronologyViolatingSet g X U :=
  mem_chronologicalFuture_of_isClosedFutureTimelikeCurve h ht

end GeneralRelativity
