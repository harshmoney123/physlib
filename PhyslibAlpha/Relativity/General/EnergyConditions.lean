/-
Copyright (c) 2026 Harsha Vankayalapati. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harsha Vankayalapati
-/
module

public import Mathlib.LinearAlgebra.Trace
public import PhyslibAlpha.Relativity.General.PointwiseCausality

/-!

# Pointwise energy conditions on a Lorentzian tangent space

The null, weak and dominant energy conditions for a stress-energy tensor `T`.

## i. Overview

On a real vector space `V` with a Lorentzian form `g` (`IsLorentzian`, signature `(-,+,+,+)`),
a stress-energy tensor at a point is a bilinear form `T`. The energy conditions are pointwise
positivity conditions on `T` against vectors of a given causal character:

- null: `T k k ≥ 0` for every null vector `k`;
- weak: `T u u ≥ 0` for every timelike vector `u`;
- dominant: `T u v ≥ 0` for all future-directed causal vectors `u`, `v`;
- strong: `(T_{ab} - T g_{ab} / (n - 2)) u^a u^b ≥ 0` for every timelike `u`.

## ii. Key results

- `NullEnergyCondition`, `WeakEnergyCondition`, `DominantEnergyCondition` : the conditions.
- `IsLorentzian.nonneg_of_isNull` : a bilinear form that is non-negative on timelike vectors is
  non-negative on null vectors.
- `WeakEnergyCondition.nullEnergyCondition` : the weak condition implies the null condition.
- `DominantEnergyCondition.weakEnergyCondition` : the dominant condition implies the weak one.
- `StrongEnergyCondition` : the strong condition, using the trace `traceForm` with respect to `g`;
  `StrongEnergyCondition.nullEnergyCondition` shows that it implies the null condition.

## iii. Table of contents

- A. The energy conditions
- B. Non-negativity on null vectors by continuity
- C. Implications between the energy conditions
- D. The strong energy condition

## iv. References

- S. W. Hawking and G. F. R. Ellis, *The Large Scale Structure of Space-Time*, Section 4.3.

-/

@[expose] public section

noncomputable section

namespace GeneralRelativity

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-!

## A. The energy conditions

-/

/-- The null energy condition: `T k k ≥ 0` for every null vector `k`. -/
def NullEnergyCondition (g T : LinearMap.BilinForm ℝ V) : Prop :=
  ∀ k, IsNull g k → 0 ≤ T k k

/-- The weak energy condition: `T u u ≥ 0` for every timelike vector `u`. -/
def WeakEnergyCondition (g T : LinearMap.BilinForm ℝ V) : Prop :=
  ∀ u, IsTimelike g u → 0 ≤ T u u

/-- The dominant energy condition: `T u v ≥ 0` for all future-directed causal vectors `u`, `v`
with respect to the time orientation `o`. -/
def DominantEnergyCondition {g : LinearMap.BilinForm ℝ V} (o : TimeOrientation g)
    (T : LinearMap.BilinForm ℝ V) : Prop :=
  ∀ u v, IsFutureCausal o u → IsFutureCausal o v → 0 ≤ T u v

/-!

## B. Non-negativity on null vectors by continuity

-/

namespace IsLorentzian

variable {g : LinearMap.BilinForm ℝ V}

/-- For a Lorentzian `g` and a null vector `k`, there is a timelike `t` with `g k t < 0`. -/
lemma exists_isTimelike_g_neg (hg : IsLorentzian g) {k : V} (hk : IsNull g k) :
    ∃ t, IsTimelike g t ∧ g k t < 0 := by
  obtain ⟨u, hu, _⟩ := hg.exists_timelike
  have hu : IsTimelike g u := hu
  have hne : g k u ≠ 0 := fun h => by
    have : 0 < g k k := hg.isSpacelike_of_orthogonal hu hk.2 (by rw [hg.symm]; exact h)
    linarith [hk.1]
  rcases lt_or_gt_of_ne hne with h | h
  · exact ⟨u, hu, h⟩
  · exact ⟨-u, by unfold IsTimelike at hu ⊢; simpa using hu, by simpa using h⟩

/-- A bilinear form which is non-negative on timelike vectors is non-negative on null vectors. -/
lemma nonneg_of_isNull (hg : IsLorentzian g) {B : LinearMap.BilinForm ℝ V}
    (h : ∀ u, IsTimelike g u → 0 ≤ B u u) {k : V} (hk : IsNull g k) : 0 ≤ B k k := by
  obtain ⟨t, ht, hkt⟩ := hg.exists_isTimelike_g_neg hk
  have hε : ∀ ε : ℝ, 0 < ε → 0 ≤ B k k + ε * (B k t + B t k) + ε ^ 2 * B t t := by
    intro ε hε
    have hu : IsTimelike g (k + ε • t) := by
      unfold IsTimelike
      have := hk.1
      have h2 : g t t < 0 := ht
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        hg.symm t k]
      nlinarith [mul_pos hε hε, mul_neg_of_pos_of_neg hε hkt]
    have := h _ hu
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] at this
    linarith
  by_contra hneg
  push Not at hneg
  set c : ℝ := |B k t + B t k| + |B t t| + 1 with hc
  have hcpos : 0 < c := by positivity
  set ε : ℝ := min 1 (-B k k / (4 * c)) with hεdef
  have hε0 : 0 < ε := lt_min one_pos (by apply div_pos <;> linarith)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hε2 : ε ≤ -B k k / (4 * c) := min_le_right _ _
  have hεc : ε * (4 * c) ≤ -B k k := (le_div_iff₀ (by positivity)).mp hε2
  have h0 := hε ε hε0
  have hb1 : ε * (B k t + B t k) ≤ ε * c := by
    apply mul_le_mul_of_nonneg_left _ hε0.le
    linarith [le_abs_self (B k t + B t k), abs_nonneg (B t t)]
  have hb2 : ε ^ 2 * B t t ≤ ε * c := by
    have : ε * B t t ≤ c := by
      calc ε * B t t ≤ ε * |B t t| := mul_le_mul_of_nonneg_left (le_abs_self _) hε0.le
        _ ≤ 1 * |B t t| := mul_le_mul_of_nonneg_right hε1 (abs_nonneg _)
        _ ≤ c := by linarith [abs_nonneg (B k t + B t k)]
    calc ε ^ 2 * B t t = ε * (ε * B t t) := by ring
      _ ≤ ε * c := mul_le_mul_of_nonneg_left this hε0.le
  linarith

/-- A Lorentzian form is non-degenerate. -/
lemma separatingLeft (hg : IsLorentzian g) : g.SeparatingLeft := by
  intro x hx
  obtain ⟨u, hu, hpos⟩ := hg.exists_timelike
  by_contra hne
  have hxu : g u x = 0 := by rw [hg.symm]; exact hx u
  have hxx : g x x = 0 := hx x
  have hu' : IsTimelike g u := hu
  -- `x` is orthogonal to the timelike `u` and nonzero, hence spacelike
  have := hg.isSpacelike_of_orthogonal hu' hne hxu
  exact absurd hxx this.ne'

/-- A Lorentzian form on a finite-dimensional space is non-degenerate. -/
lemma nondegenerate [FiniteDimensional ℝ V] (hg : IsLorentzian g) : g.Nondegenerate :=
  LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft hg.separatingLeft

end IsLorentzian

/-!

## C. Implications between the energy conditions

-/

/-- The weak energy condition implies the null energy condition. -/
lemma WeakEnergyCondition.nullEnergyCondition {g T : LinearMap.BilinForm ℝ V}
    (hg : IsLorentzian g) (h : WeakEnergyCondition g T) : NullEnergyCondition g T :=
  fun _ hk => hg.nonneg_of_isNull h hk

/-- The dominant energy condition implies the weak energy condition. -/
lemma DominantEnergyCondition.weakEnergyCondition {g T : LinearMap.BilinForm ℝ V}
    (hg : IsLorentzian g) {o : TimeOrientation g} (h : DominantEnergyCondition o T) :
    WeakEnergyCondition g T := by
  intro u hu
  rcases hg.isFutureTimelike_or_neg o hu with hf | hf
  · exact h u u hf.isFutureCausal hf.isFutureCausal
  · simpa using h (-u) (-u) hf.isFutureCausal hf.isFutureCausal

/-- The dominant energy condition implies the null energy condition. -/
lemma DominantEnergyCondition.nullEnergyCondition {g T : LinearMap.BilinForm ℝ V}
    (hg : IsLorentzian g) {o : TimeOrientation g} (h : DominantEnergyCondition o T) :
    NullEnergyCondition g T :=
  (h.weakEnergyCondition hg).nullEnergyCondition hg

/-!

## D. The strong energy condition

-/

section Strong

variable [FiniteDimensional ℝ V]

/-- The trace `g^{ab} T_{ab}` of a bilinear form `T` with respect to a non-degenerate `g`, the
trace of the endomorphism obtained by raising the first index of `T` with `g`. -/
def traceForm (g : LinearMap.BilinForm ℝ V) (hn : g.Nondegenerate)
    (T : LinearMap.BilinForm ℝ V) : ℝ :=
  LinearMap.trace ℝ V ((g.toDual hn).symm.toLinearMap ∘ₗ T)

/-- The strong energy condition: `(T_{ab} - T g_{ab} / (n - 2)) u^a u^b ≥ 0` for every timelike
`u`, where `T = g^{ab} T_{ab}` and `n` is the dimension. For `n = 4` this is
`(T_{ab} - T g_{ab} / 2) u^a u^b ≥ 0`. -/
def StrongEnergyCondition (g : LinearMap.BilinForm ℝ V) (hn : g.Nondegenerate)
    (T : LinearMap.BilinForm ℝ V) : Prop :=
  ∀ u, IsTimelike g u →
    0 ≤ T u u - traceForm g hn T / ((Module.finrank ℝ V : ℝ) - 2) * g u u

/-- The strong energy condition implies the null energy condition. -/
lemma StrongEnergyCondition.nullEnergyCondition {g T : LinearMap.BilinForm ℝ V}
    (hg : IsLorentzian g) {hn : g.Nondegenerate} (h : StrongEnergyCondition g hn T) :
    NullEnergyCondition g T := by
  intro k hk
  have := hg.nonneg_of_isNull
    (B := T - (traceForm g hn T / ((Module.finrank ℝ V : ℝ) - 2)) • g) h hk
  simpa [hk.1] using this

end Strong

end GeneralRelativity
