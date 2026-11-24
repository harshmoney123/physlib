/-
Copyright (c) 2026 Harsha Vankayalapati. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harsha Vankayalapati
-/
module

public import Physlib.Cosmology.FLRW.EnergyConditions
public import PhyslibAlpha.Relativity.General.EnergyConditions

/-!

# Energy conditions of a perfect fluid

The FLRW energy conditions of a cosmic fluid are the energy conditions of a perfect fluid.

## i. Overview

A perfect fluid with four-velocity `x`, mass density `ρ` and pressure `p` has, in the signature
`(+,-,-,-)` of `PhyslibAlpha.Relativity.General.PointwiseCausality`, the stress-energy tensor
`T_{ab} = (ρ + p / c²) x_a x_b - p g_{ab}`. Here `c : SpeedOfLight` is the speed of light (take
`c = 1` for units in which it is one), the four-velocity is normalised to `g x x = c²`, and, as
for a `CosmicFluid` in `Physlib.Cosmology.FLRW.Basic`, `ρ` and `p / c²` have the same dimension:
the energy density seen by the fluid is `T(x, x) / c² = ρ c²`.

We show that the pointwise energy conditions of
`PhyslibAlpha.Relativity.General.EnergyConditions` for this tensor are equivalent to the
conditions on `ρ` and `p` that define the energy conditions of a `CosmicFluid` in
`Physlib.Cosmology.FLRW.EnergyConditions`. The null, weak and dominant conditions are treated on a
Lorentzian space containing a spacelike direction orthogonal to `x`, and the strong condition on
a four-dimensional space.

## ii. Key results

- `perfectFluid` : the stress-energy tensor of a perfect fluid.
- `CosmicFluid.stressEnergy` : the stress-energy tensor of a cosmic fluid at a time `t`.
- `nullEnergyCondition_perfectFluid_iff`, `weakEnergyCondition_perfectFluid_iff`,
  `dominantEnergyCondition_perfectFluid_iff`, `strongEnergyCondition_perfectFluid_iff` : the
  energy conditions of the perfect fluid tensor are conditions on `ρ` and `p`.
- `CosmicFluid.nullEnergyCondition_stressEnergy_iff`,
  `CosmicFluid.weakEnergyCondition_stressEnergy_iff`,
  `CosmicFluid.dominantEnergyCondition_stressEnergy_iff`,
  `CosmicFluid.strongEnergyCondition_stressEnergy_iff` : these are exactly the energy conditions
  of a `CosmicFluid`.

## iii. Table of contents

- A. The perfect fluid tensor
- B. Auxiliary vectors
- C. The null energy condition
- D. The weak energy condition
- E. The dominant energy condition
- F. The strong energy condition
- G. The energy conditions of a cosmic fluid

## iv. References

- S. W. Hawking and G. F. R. Ellis, *The Large Scale Structure of Space-Time*, Section 3.3 (in
  the opposite sign convention `(-,+,+,+)` and units with `c = 1`).

-/

@[expose] public section

noncomputable section

namespace GeneralRelativity

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-!

## A. The perfect fluid tensor

-/

/-- The stress-energy tensor `T_{ab} = (ρ + p / c²) x_a x_b - p g_{ab}` of a perfect fluid, for a
metric `g` of signature `(+,-,-,-)`.

- `x : V` is the four-velocity, normalised to `g x x = c²`.
- `ρ : ℝ` is the mass density, as for a `CosmicFluid`: the energy density is `ρ c²`.
- `p : ℝ` is the pressure.
- `c : SpeedOfLight` is the speed of light; take `c = 1` for units in which it is one. -/
def perfectFluid (g : LinearMap.BilinForm ℝ V) (x : V) (ρ p : ℝ) (c : SpeedOfLight) :
    LinearMap.BilinForm ℝ V :=
  (ρ + p / (c : ℝ) ^ 2) • (g x).smulRight (g x) - p • g

lemma perfectFluid_apply (g : LinearMap.BilinForm ℝ V) (x : V) (ρ p : ℝ) (c : SpeedOfLight)
    (v w : V) : perfectFluid g x ρ p c v w =
      (ρ + p / (c : ℝ) ^ 2) * (g x v * g x w) - p * g v w := by
  simp [perfectFluid]

/-!

## B. Auxiliary vectors

-/

/-- A four-velocity, normalised to `g x x = c²`, is timelike. -/
private lemma isTimelike_of_eq_sq {g : LinearMap.BilinForm ℝ V} {x : V} {c : SpeedOfLight}
    (hx : g x x = (c : ℝ) ^ 2) : IsTimelike g x := by
  unfold IsTimelike
  rw [hx]
  exact pow_pos c.val_pos 2

namespace IsLorentzian

variable {g : LinearMap.BilinForm ℝ V} {x : V} {c : SpeedOfLight}

/-- A spacelike vector `e` orthogonal to a four-velocity `x` and normalised to `g e e = -c²`,
given some nonzero orthogonal vector. -/
lemma exists_unit_orthogonal (hg : IsLorentzian g) (hx : g x x = (c : ℝ) ^ 2)
    (he : ∃ e, e ≠ 0 ∧ g x e = 0) : ∃ e, g x e = 0 ∧ g e e = -(c : ℝ) ^ 2 := by
  obtain ⟨e₀, hne, hxe⟩ := he
  have hneg : g e₀ e₀ < 0 := hg.isSpacelike_of_orthogonal (isTimelike_of_eq_sq hx) hne hxe
  refine ⟨((c : ℝ) / Real.sqrt (-g e₀ e₀)) • e₀, ?_, ?_⟩
  · simp [hxe]
  · simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    have hs : Real.sqrt (-g e₀ e₀) ^ 2 = -g e₀ e₀ := Real.sq_sqrt (by linarith)
    calc _ = (c : ℝ) ^ 2 * (g e₀ e₀ / Real.sqrt (-g e₀ e₀) ^ 2) := by ring
      _ = _ := by rw [hs, div_neg, div_self hneg.ne, mul_neg, mul_one]

/-- If `x` is future-directed timelike and a causal `w` has `0 < g x w`, then `w` is
future-directed. -/
lemma isFutureCausal_of_g_pos (hg : IsLorentzian g) {o : TimeOrientation g}
    (hx : IsFutureTimelike o x) {w : V} (hw : IsCausal g w) (h : 0 < g x w) :
    IsFutureCausal o w := by
  rcases hg.isFutureCausal_or_isPastCausal o hw with hf | hp
  · exact hf
  · have := hg.g_nonneg_of_isFutureCausal hx.isFutureCausal (isPastCausal_iff_neg.mp hp)
    simp only [map_neg] at this
    linarith

end IsLorentzian

end GeneralRelativity

namespace Cosmology.CosmicFluid

open GeneralRelativity

/-- The stress-energy tensor of a cosmic fluid `F` at time `t`, as a perfect fluid with
four-velocity `x`, `c : SpeedOfLight` being the speed of light. -/
def stressEnergy {V : Type*} [AddCommGroup V] [Module ℝ V] (F : CosmicFluid)
    (g : LinearMap.BilinForm ℝ V) (x : V) (c : SpeedOfLight) (t : Time) :
    LinearMap.BilinForm ℝ V :=
  perfectFluid g x (F.ρ t) (F.p t) c

end Cosmology.CosmicFluid

/-!

## C. The null energy condition

-/

namespace GeneralRelativity

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable {g : LinearMap.BilinForm ℝ V} {x : V} {c : SpeedOfLight} {ρ p : ℝ}

/-- For a four-velocity `x` and an orthogonal `e` with `g e e = -c²`, the vector `x + e` is null
and `g x (x + e) = c²`. -/
private lemma isNull_add_unit_orthogonal (hg : IsLorentzian g) (hx : g x x = (c : ℝ) ^ 2) {e : V}
    (hxe : g x e = 0) (hee : g e e = -(c : ℝ) ^ 2) :
    IsNull g (x + e) ∧ g x (x + e) = (c : ℝ) ^ 2 := by
  have h1 : g x (x + e) = (c : ℝ) ^ 2 := by simp [hx, hxe]
  refine ⟨⟨by simp [hx, hxe, hee, hg.symm e x], fun h0 => ?_⟩, h1⟩
  rw [h0, map_zero] at h1
  exact (pow_pos c.val_pos 2).ne h1

/-- The null energy condition of a perfect fluid is `0 ≤ ρ + p / c²`. -/
lemma nullEnergyCondition_perfectFluid_iff (hg : IsLorentzian g) (hx : g x x = (c : ℝ) ^ 2)
    (he : ∃ e, e ≠ 0 ∧ g x e = 0) :
    NullEnergyCondition g (perfectFluid g x ρ p c) ↔ 0 ≤ ρ + p / (c : ℝ) ^ 2 := by
  have hc : 0 < (c : ℝ) ^ 2 := by have := c.val_pos; positivity
  constructor
  · intro h
    obtain ⟨e, hxe, hee⟩ := hg.exists_unit_orthogonal hx he
    obtain ⟨hk, h1⟩ := isNull_add_unit_orthogonal hg hx hxe hee
    have := h _ hk
    rw [perfectFluid_apply, h1, hk.1] at this
    by_contra hneg
    push Not at hneg
    nlinarith [mul_neg_of_neg_of_pos hneg (mul_pos hc hc)]
  · intro h k hk
    rw [perfectFluid_apply, hk.1]
    have := mul_nonneg h (mul_self_nonneg (g x k))
    linarith

/-!

## D. The weak energy condition

-/

/-- The weak energy condition of a perfect fluid is `0 ≤ ρ ∧ 0 ≤ ρ + p / c²`. -/
lemma weakEnergyCondition_perfectFluid_iff (hg : IsLorentzian g) (hx : g x x = (c : ℝ) ^ 2)
    (he : ∃ e, e ≠ 0 ∧ g x e = 0) :
    WeakEnergyCondition g (perfectFluid g x ρ p c) ↔ 0 ≤ ρ ∧ 0 ≤ ρ + p / (c : ℝ) ^ 2 := by
  have hc : 0 < (c : ℝ) ^ 2 := by have := c.val_pos; positivity
  have hxt : IsTimelike g x := isTimelike_of_eq_sq hx
  have hac : (ρ + p / (c : ℝ) ^ 2) * (c : ℝ) ^ 2 = ρ * (c : ℝ) ^ 2 + p := by field_simp
  constructor
  · intro h
    refine ⟨?_, (nullEnergyCondition_perfectFluid_iff hg hx he).mp
      (WeakEnergyCondition.nullEnergyCondition hg h)⟩
    have h1 := h x hxt
    rw [perfectFluid_apply, hx] at h1
    by_contra hneg
    push Not at hneg
    have e1 : (ρ + p / (c : ℝ) ^ 2) * ((c : ℝ) ^ 2 * (c : ℝ) ^ 2) - p * (c : ℝ) ^ 2 =
        ρ * ((c : ℝ) ^ 2 * (c : ℝ) ^ 2) := by
      linear_combination (c : ℝ) ^ 2 * hac
    nlinarith [mul_neg_of_neg_of_pos hneg (mul_pos hc hc)]
  · rintro ⟨hρ, ha⟩ v hv
    have hcs := hg.mul_self_le_sq_of_isTimelike hxt v
    rw [hx] at hcs
    rw [perfectFluid_apply]
    have key := mul_le_mul_of_nonneg_left (show (c : ℝ) ^ 2 * g v v ≤ g x v * g x v by nlinarith)
      ha
    have e1 : (ρ + p / (c : ℝ) ^ 2) * ((c : ℝ) ^ 2 * g v v) = (ρ * (c : ℝ) ^ 2 + p) * g v v := by
      rw [← hac]; ring
    have hv' : 0 < g v v := hv
    nlinarith [mul_nonneg (mul_nonneg hρ hc.le) hv'.le]

/-!

## E. The dominant energy condition

-/

/-- A non-negativity estimate for the dominant energy condition of a perfect fluid. -/
private lemma dominant_aux {ρ p c2 P Q : ℝ} (hc : 0 < c2) (hp : |p| ≤ ρ * c2)
    (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hQ2 : c2 * Q ≤ 2 * P) :
    0 ≤ (ρ + p / c2) * P - p * Q := by
  have hac : (ρ + p / c2) * c2 = ρ * c2 + p := by field_simp
  have h1 := (abs_le.mp hp).1
  have h2 := (abs_le.mp hp).2
  by_contra hneg
  push Not at hneg
  rcases le_total 0 p with h0 | h0
  · nlinarith [mul_nonneg h0 (show 0 ≤ 2 * P - c2 * Q by linarith),
      mul_nonneg hP (sub_nonneg.mpr h2)]
  · have : 0 ≤ (ρ + p / c2) := by
      have : 0 ≤ (ρ + p / c2) * c2 := by rw [hac]; linarith
      exact nonneg_of_mul_nonneg_left this hc
    nlinarith [mul_nonneg this hP, mul_nonneg (neg_nonneg.mpr h0) hQ]

/-- For a future-directed four-velocity `x` and a future-directed causal `v`, the reflection of
`v` in the orthogonal complement of `x`, reversed, is future-directed causal, and its product
with a future-directed causal `u` bounds `c² g u v` by `2 (g x u) (g x v)`. -/
private lemma dominant_reflection (hg : IsLorentzian g) (hx : g x x = (c : ℝ) ^ 2)
    {o : TimeOrientation g} (hxo : IsFutureTimelike o x) {u v : V} (hu : IsFutureCausal o u)
    (hv : IsFutureCausal o v) (hAv : 0 < g x v) :
    (c : ℝ) ^ 2 * g u v ≤ 2 * (g x u * g x v) := by
  have hc : 0 < (c : ℝ) ^ 2 := by have := c.val_pos; positivity
  obtain ⟨w, hwdef⟩ : ∃ w, w = v - (2 * g x v / (c : ℝ) ^ 2) • x := ⟨_, rfl⟩
  have hgx : g x w = -g x v := by
    simp only [hwdef, map_sub, map_smul, smul_eq_mul, hx]
    field_simp
    ring
  have hww : g w w = g v v := by
    simp only [hwdef, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
      hx, hg.symm x v]
    field_simp
    ring
  have hw : IsFutureCausal o (-w) := by
    refine hg.isFutureCausal_of_g_pos hxo ⟨?_, ?_⟩ ?_
    · simpa [hww] using hv.1.1
    · intro h0
      have := congrArg (g x) (neg_eq_zero.mp h0)
      rw [hgx, map_zero] at this
      linarith
    · simp only [map_neg, hgx]
      linarith
  have hG := hg.g_nonneg_of_isFutureCausal hu hw
  have huw : g u w = g u v - (2 * g x v / (c : ℝ) ^ 2) * g x u := by
    simp only [hwdef, map_sub, map_smul, smul_eq_mul, hg.symm u x]
  simp only [map_neg, huw] at hG
  have : 0 ≤ (c : ℝ) ^ 2 * ((2 * g x v / (c : ℝ) ^ 2) * g x u - g u v) :=
    mul_nonneg hc.le (by linarith)
  have e1 : (c : ℝ) ^ 2 * ((2 * g x v / (c : ℝ) ^ 2) * g x u - g u v) =
      2 * (g x u * g x v) - (c : ℝ) ^ 2 * g u v := by field_simp
  linarith

/-- The dominant energy condition of a perfect fluid is `0 ≤ ρ ∧ |p| ≤ ρ c²`. -/
lemma dominantEnergyCondition_perfectFluid_iff (hg : IsLorentzian g) (hx : g x x = (c : ℝ) ^ 2)
    (he : ∃ e, e ≠ 0 ∧ g x e = 0) {o : TimeOrientation g} (hxo : IsFutureTimelike o x) :
    DominantEnergyCondition o (perfectFluid g x ρ p c) ↔ 0 ≤ ρ ∧ |p| ≤ ρ * (c : ℝ) ^ 2 := by
  have hc : 0 < (c : ℝ) ^ 2 := by have := c.val_pos; positivity
  have hac : (ρ + p / (c : ℝ) ^ 2) * (c : ℝ) ^ 2 = ρ * (c : ℝ) ^ 2 + p := by field_simp
  have hxt : IsTimelike g x := hxo.1
  -- `x + e` is future-directed null for an orthogonal `e` with `g e e = -c²`
  have hnull : ∀ e, g x e = 0 → g e e = -(c : ℝ) ^ 2 → IsFutureCausal o (x + e) := by
    intro e hxe hee
    obtain ⟨hk, h1⟩ := isNull_add_unit_orthogonal hg hx hxe hee
    exact hg.isFutureCausal_of_g_pos hxo ⟨hk.1.ge, hk.2⟩ (by rw [h1]; exact hc)
  -- a future-directed causal vector has positive product with `x`
  have hpos : ∀ u, IsFutureCausal o u → 0 < g x u := fun u hu =>
    lt_of_le_of_ne (hg.g_nonneg_of_isFutureCausal hxo.isFutureCausal hu) fun h0 =>
      absurd hu.1.1 (not_le.mpr (hg.isSpacelike_of_orthogonal hxt hu.1.2 h0.symm))
  constructor
  · intro h
    obtain ⟨hρ, ha⟩ := (weakEnergyCondition_perfectFluid_iff hg hx he).mp
      (h.weakEnergyCondition hg)
    obtain ⟨e, hxe, hee⟩ := hg.exists_unit_orthogonal hx he
    have hne : g x (-e) = 0 ∧ g (-e) (-e) = -(c : ℝ) ^ 2 := ⟨by simp [hxe], by simp [hee]⟩
    have h1 := h _ _ (hnull e hxe hee) (hnull (-e) hne.1 hne.2)
    rw [perfectFluid_apply] at h1
    simp only [map_add, map_neg, LinearMap.add_apply, hx, hxe, hee,
      hg.symm e x, add_zero, neg_zero] at h1
    refine ⟨hρ, abs_le.mpr ⟨by nlinarith, ?_⟩⟩
    by_contra hneg
    push Not at hneg
    nlinarith [mul_pos hc (sub_pos.mpr hneg)]
  · rintro ⟨hρ, hp⟩ u v hu hv
    rw [perfectFluid_apply]
    exact dominant_aux hc hp (mul_pos (hpos u hu) (hpos v hv)).le
      (hg.g_nonneg_of_isFutureCausal hu hv) (dominant_reflection hg hx hxo hu hv (hpos v hv))

/-!

## F. The strong energy condition

-/

section Strong

variable [FiniteDimensional ℝ V]

/-- The trace of a perfect fluid tensor is `(ρ + p / c²) g x x - n p`, `n` being the dimension. -/
lemma traceForm_perfectFluid (hn : g.Nondegenerate) :
    traceForm g hn (perfectFluid g x ρ p c) =
      (ρ + p / (c : ℝ) ^ 2) * g x x - p * Module.finrank ℝ V := by
  have h1 : (g.toDual hn).symm.toLinearMap ∘ₗ (g x).smulRight (g x) =
      (g x).smulRight x := by
    ext v
    simp only [LinearMap.comp_apply, LinearMap.smulRight_apply, map_smul, LinearEquiv.coe_coe]
    congr 1
    exact (LinearEquiv.symm_apply_eq _).mpr rfl
  have h2 : (g.toDual hn).symm.toLinearMap ∘ₗ g = LinearMap.id := by
    ext v
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.id_apply]
    exact (LinearEquiv.symm_apply_eq _).mpr rfl
  unfold traceForm perfectFluid
  rw [LinearMap.comp_sub, LinearMap.comp_smul, LinearMap.comp_smul, h1, h2, map_sub, map_smul,
    map_smul, LinearMap.trace_smulRight, LinearMap.trace_id]
  simp

/-- The strong energy condition of a perfect fluid in four dimensions is
`0 ≤ ρ + p / c² ∧ 0 ≤ ρ + 3 p / c²`. -/
lemma strongEnergyCondition_perfectFluid_iff (hg : IsLorentzian g) (hx : g x x = (c : ℝ) ^ 2)
    (he : ∃ e, e ≠ 0 ∧ g x e = 0) (hdim : Module.finrank ℝ V = 4) :
    StrongEnergyCondition g hg.nondegenerate (perfectFluid g x ρ p c) ↔
      0 ≤ ρ + p / (c : ℝ) ^ 2 ∧ 0 ≤ ρ + 3 * p / (c : ℝ) ^ 2 := by
  have hc : 0 < (c : ℝ) ^ 2 := by have := c.val_pos; positivity
  have hxt : IsTimelike g x := isTimelike_of_eq_sq hx
  have hac : (ρ + p / (c : ℝ) ^ 2) * (c : ℝ) ^ 2 = ρ * (c : ℝ) ^ 2 + p := by field_simp
  have hbc : (ρ + 3 * p / (c : ℝ) ^ 2) * (c : ℝ) ^ 2 = ρ * (c : ℝ) ^ 2 + 3 * p := by field_simp
  have htr : traceForm g hg.nondegenerate (perfectFluid g x ρ p c) / ((Module.finrank ℝ V : ℝ) - 2)
      = (ρ * (c : ℝ) ^ 2 - 3 * p) / 2 := by
    rw [traceForm_perfectFluid, hdim, hx]
    push_cast
    linear_combination (1 / 2 : ℝ) * hac
  constructor
  · intro h
    refine ⟨(nullEnergyCondition_perfectFluid_iff hg hx he).mp
      (StrongEnergyCondition.nullEnergyCondition hg h), ?_⟩
    have h1 := h x hxt
    rw [htr, perfectFluid_apply, hx] at h1
    by_contra hneg
    push Not at hneg
    nlinarith [mul_neg_of_neg_of_pos hneg (mul_pos hc hc)]
  · rintro ⟨ha, hb⟩ v hv
    rw [htr, perfectFluid_apply]
    have hcs := hg.mul_self_le_sq_of_isTimelike hxt v
    rw [hx] at hcs
    have key := mul_le_mul_of_nonneg_left (show (c : ℝ) ^ 2 * g v v ≤ g x v * g x v by nlinarith)
      ha
    have e1 : (ρ + p / (c : ℝ) ^ 2) * ((c : ℝ) ^ 2 * g v v) = (ρ * (c : ℝ) ^ 2 + p) * g v v := by
      rw [← hac]; ring
    have hv' : 0 < g v v := hv
    have hb' : 0 ≤ ρ * (c : ℝ) ^ 2 + 3 * p := by rw [← hbc]; positivity
    nlinarith [mul_nonneg hv'.le hb']

end Strong

end GeneralRelativity

/-!

## G. The energy conditions of a cosmic fluid

-/

namespace Cosmology.CosmicFluid

open GeneralRelativity

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {g : LinearMap.BilinForm ℝ V} {x : V}
  {c : SpeedOfLight} (F : CosmicFluid) (t : Time)

/-- The null energy condition of the stress-energy tensor of a cosmic fluid is the null energy
condition of the cosmic fluid. -/
lemma nullEnergyCondition_stressEnergy_iff (hg : IsLorentzian g) (hx : g x x = (c : ℝ) ^ 2)
    (he : ∃ e, e ≠ 0 ∧ g x e = 0) :
    GeneralRelativity.NullEnergyCondition g (F.stressEnergy g x c t) ↔ F.NullEnergyCondition c t :=
  nullEnergyCondition_perfectFluid_iff hg hx he

/-- The weak energy condition of the stress-energy tensor of a cosmic fluid is the weak energy
condition of the cosmic fluid. -/
lemma weakEnergyCondition_stressEnergy_iff (hg : IsLorentzian g) (hx : g x x = (c : ℝ) ^ 2)
    (he : ∃ e, e ≠ 0 ∧ g x e = 0) :
    GeneralRelativity.WeakEnergyCondition g (F.stressEnergy g x c t) ↔ F.WeakEnergyCondition c t :=
  weakEnergyCondition_perfectFluid_iff hg hx he

/-- The dominant energy condition of the stress-energy tensor of a cosmic fluid is the dominant
energy condition of the cosmic fluid. -/
lemma dominantEnergyCondition_stressEnergy_iff (hg : IsLorentzian g) (hx : g x x = (c : ℝ) ^ 2)
    (he : ∃ e, e ≠ 0 ∧ g x e = 0) {o : TimeOrientation g} (hxo : IsFutureTimelike o x) :
    GeneralRelativity.DominantEnergyCondition o (F.stressEnergy g x c t) ↔
      F.DominantEnergyCondition c t :=
  dominantEnergyCondition_perfectFluid_iff hg hx he hxo

/-- The strong energy condition of the stress-energy tensor of a cosmic fluid in four dimensions
is the strong energy condition of the cosmic fluid. -/
lemma strongEnergyCondition_stressEnergy_iff [FiniteDimensional ℝ V] (hg : IsLorentzian g)
    (hx : g x x = (c : ℝ) ^ 2) (he : ∃ e, e ≠ 0 ∧ g x e = 0)
    (hdim : Module.finrank ℝ V = 4) :
    GeneralRelativity.StrongEnergyCondition g hg.nondegenerate (F.stressEnergy g x c t) ↔
      F.StrongEnergyCondition c t :=
  strongEnergyCondition_perfectFluid_iff hg hx he hdim

end Cosmology.CosmicFluid
