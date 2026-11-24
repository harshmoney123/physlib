/-
Copyright (c) 2026 Harsha Vankayalapati. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harsha Vankayalapati
-/
module

public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.LinearAlgebra.BilinearForm.Basic
public import Mathlib.Algebra.QuadraticDiscriminant
public import Physlib.Relativity.Causality.TimeLike

/-!

# Pointwise Lorentzian geometry on a tangent space

Causal character of vectors for a bilinear form of signature `(-,+,+,+)`.

## i. Overview

A tangent space of a spacetime carries a Lorentzian inner product `g`, with the sign convention
`(-,+,+,+)`. Here we work on an arbitrary real vector space `V` with a symmetric bilinear form `g`,
and say that `g` is Lorentzian (`IsLorentzian`) when some vector `u` has `g u u < 0` and `g` is
positive definite on the `g`-orthogonal complement of `u`. This is exactly signature
`(-,+,+,+)`, in any dimension, and non-degeneracy is a consequence.

Vectors are classified as timelike, null, spacelike or causal. A time orientation is a choice of
reference timelike vector `T`; a causal vector is future (past) directed if its product with `T` is
negative (positive). Physlib's Minkowski product on `Lorentz.Vector d` is in the `+---`
convention, so `-⟪·, ·⟫ₘ` is Lorentzian (`isLorentzian_minkowski`).

## ii. Key results

- `IsLorentzian` : the signature condition.
- `IsTimelike`, `IsNull`, `IsSpacelike`, `IsCausal` : the causal character of a vector.
- `TimeOrientation`, `IsFutureTimelike`, `IsFutureCausal`, `IsPastCausal` : time orientation.
- `IsLorentzian.isSpacelike_of_orthogonal` : a nonzero vector orthogonal to a timelike vector
  is spacelike.
- `IsLorentzian.mul_self_le_sq_of_isTimelike` : reversed Cauchy-Schwarz for timelike vectors.
- `IsLorentzian.mul_self_eq_sq_iff` : equality in reversed Cauchy-Schwarz iff the vectors are proportional.
- `IsLorentzian.isFutureTimelike_add` : the sum of future-directed timelike vectors is
  future-directed timelike.
- `IsLorentzian.isFutureCausal_add` : the same for future-directed causal vectors.
- `IsLorentzian.isFutureCausal_or_isPastCausal`, `IsLorentzian.isPastCausal_iff_neg` : every causal vector is
  future- or past-directed, and past-directed means negative of future-directed.
- `isLorentzian_minkowski` : the Minkowski metric is Lorentzian.

## iii. Table of contents

- A. Signature and causal character
- B. Orthogonal complements of timelike vectors
- C. Reversed Cauchy-Schwarz
- D. Time orientation
- E. The Minkowski metric

## iv. References

- B. O'Neill, *Semi-Riemannian Geometry*, Chapter 5.

-/

@[expose] public section

noncomputable section

namespace GeneralRelativity

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-!

## A. Signature and causal character

-/

/-- A symmetric bilinear form `g` on `V` has signature `(-,+,+,+)` if some vector `u` satisfies
`g u u < 0` and `g` is positive definite on the `g`-orthogonal complement of `u`. -/
structure IsLorentzian (g : LinearMap.BilinForm ℝ V) : Prop where
  /-- The form is symmetric. -/
  symm : ∀ v w, g v w = g w v
  /-- A timelike vector whose orthogonal complement is positive definite. -/
  exists_timelike : ∃ u, g u u < 0 ∧ ∀ v, g u v = 0 → v ≠ 0 → 0 < g v v

/-- A vector is timelike if `g v v < 0`. -/
def IsTimelike (g : LinearMap.BilinForm ℝ V) (v : V) : Prop := g v v < 0

/-- A vector is null if it is nonzero and `g v v = 0`. -/
def IsNull (g : LinearMap.BilinForm ℝ V) (v : V) : Prop := g v v = 0 ∧ v ≠ 0

/-- A vector is spacelike if `0 < g v v`. The zero vector is not spacelike. -/
def IsSpacelike (g : LinearMap.BilinForm ℝ V) (v : V) : Prop := 0 < g v v

/-- A vector is causal if it is nonzero and `g v v ≤ 0`, i.e. timelike or null. -/
def IsCausal (g : LinearMap.BilinForm ℝ V) (v : V) : Prop := g v v ≤ 0 ∧ v ≠ 0

lemma IsTimelike.isCausal {g : LinearMap.BilinForm ℝ V} {v : V} (h : IsTimelike g v) :
    IsCausal g v :=
  ⟨h.le, fun hv => by simp [hv, IsTimelike] at h⟩

lemma isCausal_iff {g : LinearMap.BilinForm ℝ V} {v : V} :
    IsCausal g v ↔ IsTimelike g v ∨ IsNull g v := by
  unfold IsCausal IsTimelike IsNull
  constructor
  · rintro ⟨h, hv⟩
    rcases h.lt_or_eq with h | h
    · exact .inl h
    · exact .inr ⟨h, hv⟩
  · rintro (h | ⟨h, hv⟩)
    · exact IsTimelike.isCausal h
    · exact ⟨h.le, hv⟩

/-!

## B. Orthogonal complements of timelike vectors

-/

namespace IsLorentzian

variable {g : LinearMap.BilinForm ℝ V}

/-- Orthogonal to the witness `u`, the form is non-negative. -/
private lemma nonneg_of_orth_witness {u : V} (hu : ∀ v, g u v = 0 → v ≠ 0 → 0 < g v v)
    {w : V} (hw : g u w = 0) : 0 ≤ g w w := by
  by_cases h : w = 0
  · simp [h]
  · exact (hu w hw h).le

/-- Cauchy-Schwarz on the orthogonal complement of the witness. -/
private lemma sq_le_of_orth_witness (hg : IsLorentzian g) {u : V}
    (hpos : ∀ v, g u v = 0 → v ≠ 0 → 0 < g v v) {x y : V} (hx : g u x = 0) (hy : g u y = 0) :
    g x y ^ 2 ≤ g x x * g y y := by
  have h : ∀ t : ℝ, 0 ≤ g y y * (t * t) + 2 * g x y * t + g x x := by
    intro t
    have hxy : g u (x + t • y) = 0 := by simp [hx, hy]
    have := nonneg_of_orth_witness hpos hxy
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      hg.symm y x] at this
    nlinarith
  have := discrim_le_zero h
  simp only [discrim] at this
  nlinarith

private lemma pos_aux {c a b gxx gyy gxy : ℝ} (hc : c < 0) (hxx : 0 ≤ gxx)
    (h1 : a ^ 2 * c + gxx < 0) (h2 : a * b * c + gxy = 0) (hcs : gxy ^ 2 ≤ gxx * gyy) (hb : b ≠ 0) :
    0 < b ^ 2 * c + gyy := by
  by_contra hcon
  have hbpos : 0 < -(b ^ 2 * c) := by
    have := pow_pos (abs_pos.mpr hb) 2
    rw [sq_abs] at this
    nlinarith
  have h3 : gxx * gyy ≤ gxx * (-(b ^ 2 * c)) := mul_le_mul_of_nonneg_left (by linarith) hxx
  have h4 : gxx * (-(b ^ 2 * c)) < (-(a ^ 2 * c)) * (-(b ^ 2 * c)) :=
    mul_lt_mul_of_pos_right (by linarith) hbpos
  have h5 : gxy = -(a * b * c) := by linarith
  subst h5
  nlinarith

/-- The form on vectors split along `u₀` and its orthogonal complement. -/
private lemma form_decomp (hg : IsLorentzian g) {u₀ x y : V} (hx : g u₀ x = 0) (hy : g u₀ y = 0)
    (p q : ℝ) : g (p • u₀ + x) (q • u₀ + y) = p * q * g u₀ u₀ + g x y := by
  have hxu : g x u₀ = 0 := by rw [hg.symm]; exact hx
  simp [hy, hxu]
  ring

/-- A nonzero vector orthogonal to a timelike vector is spacelike. -/
lemma isSpacelike_of_orthogonal (hg : IsLorentzian g) {u v : V} (hu : IsTimelike g u)
    (hv : v ≠ 0) (horth : g u v = 0) : IsSpacelike g v := by
  obtain ⟨u₀, hu₀, hpos⟩ := hg.exists_timelike
  have hdec : ∀ w : V, g u₀ (w - (g u₀ w / g u₀ u₀) • u₀) = 0 := by
    intro w
    have hne : g u₀ u₀ ≠ 0 := hu₀.ne
    simp only [map_sub, map_smul, smul_eq_mul]
    field_simp
    ring
  set a := g u₀ u / g u₀ u₀
  set b := g u₀ v / g u₀ u₀
  have hx := hdec u
  have hy := hdec v
  set x := u - a • u₀
  set y := v - b • u₀
  have hux : u = a • u₀ + x := by simp [x]
  have hvy : v = b • u₀ + y := by simp [y]
  have huu : g u u = a * a * g u₀ u₀ + g x x := by
    conv_lhs => rw [hux]
    rw [form_decomp hg hx hx]
  have huv : g u v = a * b * g u₀ u₀ + g x y := by
    conv_lhs => rw [hux, hvy]
    rw [form_decomp hg hx hy]
  have hvv : g v v = b * b * g u₀ u₀ + g y y := by
    conv_lhs => rw [hvy]
    rw [form_decomp hg hy hy]
  have hxx : 0 ≤ g x x := nonneg_of_orth_witness hpos hx
  have hcs := sq_le_of_orth_witness hg hpos hx hy
  unfold IsSpacelike
  by_cases hb0 : b = 0
  · have hyv : y = v := by simp [y, hb0]
    rw [← hyv]
    exact hpos y hy (hyv ▸ hv)
  · have hu' : a * a * g u₀ u₀ + g x x < 0 := huu ▸ hu
    have := pos_aux hu₀ hxx (a := a) (b := b) (by nlinarith) (by rw [horth] at huv; linarith)
      hcs hb0
    rw [hvv]
    nlinarith

/-- On the orthogonal complement of a timelike vector the form is non-negative. -/
lemma nonneg_of_orthogonal (hg : IsLorentzian g) {u w : V} (hu : IsTimelike g u)
    (horth : g u w = 0) : 0 ≤ g w w := by
  by_cases hw : w = 0
  · simp [hw]
  · exact (hg.isSpacelike_of_orthogonal hu hw horth).le

/-- Cauchy-Schwarz on the orthogonal complement of a timelike vector. -/
lemma sq_le_of_orthogonal (hg : IsLorentzian g) {u x y : V} (hu : IsTimelike g u)
    (hx : g u x = 0) (hy : g u y = 0) : g x y ^ 2 ≤ g x x * g y y :=
  sq_le_of_orth_witness hg (fun _ h hv => hg.isSpacelike_of_orthogonal hu hv h) hx hy

/-!

## C. Reversed Cauchy-Schwarz

-/

/-- Split `v` along a timelike `u` and its orthogonal complement. -/
private lemma exists_orth_decomp {u : V} (hu : IsTimelike g u) (v : V) :
    ∃ (a : ℝ) (w : V), g u w = 0 ∧ v = a • u + w ∧ g u v = a * g u u := by
  have hne : g u u ≠ 0 := hu.ne
  have hav : g u v / g u u * g u u = g u v := div_mul_cancel₀ _ hne
  refine ⟨g u v / g u u, v - (g u v / g u u) • u, ?_, by simp, hav.symm⟩
  simp only [map_sub, map_smul, smul_eq_mul]
  linarith

/-- Reversed Cauchy-Schwarz: for timelike `u` and any `v`, `g u u * g v v ≤ (g u v) ^ 2`. In
particular it holds for two timelike vectors. -/
lemma mul_self_le_sq_of_isTimelike (hg : IsLorentzian g) {u : V} (hu : IsTimelike g u) (v : V) :
    g u u * g v v ≤ g u v ^ 2 := by
  obtain ⟨a, w, hw, hdec, huv⟩ := exists_orth_decomp hu v
  have hnn := hg.nonneg_of_orthogonal hu hw
  have hvv : g v v = a * a * g u u + g w w := by
    conv_lhs => rw [hdec]
    rw [form_decomp hg hw hw]
  rw [hvv, huv]
  have : g u u * g w w ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hu.le hnn
  nlinarith

/-- Equality in the reversed Cauchy-Schwarz inequality for a timelike `u` holds exactly when `v`
is proportional to `u`. -/
lemma mul_self_eq_sq_iff (hg : IsLorentzian g) {u : V} (hu : IsTimelike g u) (v : V) :
    g u u * g v v = g u v ^ 2 ↔ ∃ a : ℝ, v = a • u := by
  constructor
  · intro h
    obtain ⟨a, w, hw, hdec, huv⟩ := exists_orth_decomp hu v
    have hvv : g v v = a * a * g u u + g w w := by
      conv_lhs => rw [hdec]
      rw [form_decomp hg hw hw]
    rw [hvv, huv] at h
    have hww : g u u * g w w = 0 := by nlinarith
    have hw0 : g w w = 0 := (mul_eq_zero.mp hww).resolve_left hu.ne
    have : w = 0 := by
      by_contra hne
      exact absurd (hg.isSpacelike_of_orthogonal hu hne hw) (by unfold IsSpacelike; linarith)
    exact ⟨a, by simp [hdec, this]⟩
  · rintro ⟨a, rfl⟩
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring

/-- The product of two timelike vectors is nonzero. -/
lemma g_ne_zero_of_isTimelike (hg : IsLorentzian g) {u v : V} (hu : IsTimelike g u)
    (hv : IsTimelike g v) : g u v ≠ 0 := by
  intro h
  have := hg.isSpacelike_of_orthogonal hu hv.isCausal.2 h
  exact absurd hv (not_lt.mpr this.le)

/-!

## D. Time orientation

-/

end IsLorentzian

/-- A time orientation on `(V, g)`, given by a reference timelike vector `T`. -/
structure TimeOrientation (g : LinearMap.BilinForm ℝ V) where
  /-- The reference timelike vector. -/
  T : V
  /-- The reference vector is timelike. -/
  isTimelike : IsTimelike g T

variable {g : LinearMap.BilinForm ℝ V}

/-- A vector is future-directed timelike if it is timelike and `g T v < 0`. -/
def IsFutureTimelike (o : TimeOrientation g) (v : V) : Prop := IsTimelike g v ∧ g o.T v < 0

/-- A vector is future-directed causal if it is causal and `g T v < 0`. -/
def IsFutureCausal (o : TimeOrientation g) (v : V) : Prop := IsCausal g v ∧ g o.T v < 0

/-- A vector is past-directed causal if it is causal and `0 < g T v`. -/
def IsPastCausal (o : TimeOrientation g) (v : V) : Prop := IsCausal g v ∧ 0 < g o.T v

lemma IsFutureTimelike.isFutureCausal {o : TimeOrientation g} {v : V}
    (h : IsFutureTimelike o v) : IsFutureCausal o v :=
  ⟨h.1.isCausal, h.2⟩

namespace IsLorentzian

/-- Two future-directed causal vectors have non-positive product, and a negative one if the
first is timelike. -/
private lemma g_nonpos_aux (hg : IsLorentzian g) {o : TimeOrientation g} {u v : V}
    (hu : IsFutureCausal o u) (hv : IsFutureCausal o v) :
    g u v ≤ 0 ∧ (IsTimelike g u → g u v < 0) := by
  set T := o.T
  have hT := o.isTimelike
  have hTT : g T T < 0 := hT
  have hTT' : g T T ≠ 0 := hTT.ne
  have hdec : ∀ w : V, g T (w - (g T w / g T T) • T) = 0 := by
    intro w
    simp only [map_sub, map_smul, smul_eq_mul]
    field_simp
    ring
  set a := g T u / g T T
  set b := g T v / g T T
  have hx := hdec u
  have hy := hdec v
  set x := u - a • T
  set y := v - b • T
  have hux : u = a • T + x := by simp [x]
  have hvy : v = b • T + y := by simp [y]
  have huu : g u u = a * a * g T T + g x x := by
    conv_lhs => rw [hux]
    rw [form_decomp hg hx hx]
  have hvv : g v v = b * b * g T T + g y y := by
    conv_lhs => rw [hvy]
    rw [form_decomp hg hy hy]
  have huv : g u v = a * b * g T T + g x y := by
    conv_lhs => rw [hux, hvy]
    rw [form_decomp hg hx hy]
  have ha : 0 < a := div_pos_of_neg_of_neg hu.2 hTT
  have hb : 0 < b := div_pos_of_neg_of_neg hv.2 hTT
  have hxx := hg.nonneg_of_orthogonal hT hx
  have hyy := hg.nonneg_of_orthogonal hT hy
  have hcs := hg.sq_le_of_orthogonal hT hx hy
  have hA : 0 < -(a * a * g T T) := by nlinarith [mul_pos ha ha]
  have hB : 0 < -(b * b * g T T) := by nlinarith [mul_pos hb hb]
  have hu' : g x x ≤ -(a * a * g T T) := by have := hu.1.1; linarith
  have hv' : g y y ≤ -(b * b * g T T) := by have := hv.1.1; linarith
  have hprod : g x y ^ 2 ≤ (-(a * a * g T T)) * (-(b * b * g T T)) :=
    hcs.trans (mul_le_mul hu' hv' hyy hA.le)
  have hpos : 0 ≤ -(a * b * g T T) := by nlinarith [mul_pos ha hb]
  have hsq : g x y ^ 2 ≤ (-(a * b * g T T)) ^ 2 := by nlinarith
  refine ⟨?_, fun hut => ?_⟩
  · have := (abs_le.mp (abs_le_of_sq_le_sq hsq hpos)).2
    rw [huv]
    linarith
  · have hu'' : g x x < -(a * a * g T T) := by
      have : g u u < 0 := hut
      linarith
    have hlt : g x x * g y y < (-(a * a * g T T)) * (-(b * b * g T T)) :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_left hv' hxx) (mul_lt_mul_of_pos_right hu'' hB)
    have hsq' : g x y ^ 2 < (-(a * b * g T T)) ^ 2 := by nlinarith
    have := (abs_lt.mp (abs_lt_of_sq_lt_sq hsq' hpos)).2
    rw [huv]
    linarith

/-- Two future-directed timelike vectors have negative product. -/
lemma g_neg_of_isFutureTimelike (hg : IsLorentzian g) {o : TimeOrientation g} {u v : V}
    (hu : IsFutureTimelike o u) (hv : IsFutureTimelike o v) : g u v < 0 :=
  (g_nonpos_aux hg hu.isFutureCausal hv.isFutureCausal).2 hu.1

/-- Two future-directed causal vectors have non-positive product. -/
lemma g_nonpos_of_isFutureCausal (hg : IsLorentzian g) {o : TimeOrientation g} {u v : V}
    (hu : IsFutureCausal o u) (hv : IsFutureCausal o v) : g u v ≤ 0 :=
  (g_nonpos_aux hg hu hv).1

/-- The sum of two future-directed causal vectors is future-directed causal. -/
lemma isFutureCausal_add (hg : IsLorentzian g) {o : TimeOrientation g} {u v : V}
    (hu : IsFutureCausal o u) (hv : IsFutureCausal o v) : IsFutureCausal o (u + v) := by
  have hT : g o.T (u + v) < 0 := by simp only [map_add]; linarith [hu.2, hv.2]
  refine ⟨⟨?_, fun h => by simp [h] at hT⟩, hT⟩
  have := hg.g_nonpos_of_isFutureCausal hu hv
  simp only [map_add, LinearMap.add_apply, hg.symm v u]
  have h1 : g u u ≤ 0 := hu.1.1
  have h2 : g v v ≤ 0 := hv.1.1
  linarith

/-- The sum of two future-directed timelike vectors is future-directed timelike. -/
lemma isFutureTimelike_add (hg : IsLorentzian g) {o : TimeOrientation g} {u v : V}
    (hu : IsFutureTimelike o u) (hv : IsFutureTimelike o v) : IsFutureTimelike o (u + v) := by
  refine ⟨?_, by simp only [map_add]; linarith [hu.2, hv.2]⟩
  have := hg.g_neg_of_isFutureTimelike hu hv
  unfold IsTimelike
  simp only [map_add, LinearMap.add_apply, hg.symm v u]
  have h1 : g u u < 0 := hu.1
  have h2 : g v v < 0 := hv.1
  linarith

/-- A vector is past-directed causal iff its negative is future-directed causal. -/
lemma isPastCausal_iff_neg {o : TimeOrientation g} {v : V} :
    IsPastCausal o v ↔ IsFutureCausal o (-v) := by
  have hc : IsCausal g (-v) ↔ IsCausal g v := by simp [IsCausal]
  simp [IsPastCausal, IsFutureCausal, hc]

/-- A causal vector is either future-directed or past-directed. -/
lemma isFutureCausal_or_isPastCausal (hg : IsLorentzian g) (o : TimeOrientation g) {v : V}
    (hv : IsCausal g v) : IsFutureCausal o v ∨ IsPastCausal o v := by
  have hne : g o.T v ≠ 0 := fun h =>
    absurd (hg.isSpacelike_of_orthogonal o.isTimelike hv.2 h) (not_lt.mpr hv.1)
  rcases lt_or_gt_of_ne hne with h | h
  · exact .inl ⟨hv, h⟩
  · exact .inr ⟨hv, h⟩

/-- A timelike vector or its negative is future-directed timelike. -/
lemma isFutureTimelike_or_neg (hg : IsLorentzian g) (o : TimeOrientation g) {v : V}
    (hv : IsTimelike g v) : IsFutureTimelike o v ∨ IsFutureTimelike o (-v) := by
  have hne := hg.g_ne_zero_of_isTimelike o.isTimelike hv
  rcases lt_or_gt_of_ne hne with h | h
  · exact .inl ⟨hv, h⟩
  · refine .inr ⟨?_, by simpa using h⟩
    unfold IsTimelike at hv ⊢
    simpa using hv

end IsLorentzian

/-!

## E. The Minkowski metric

-/

open Lorentz Vector in
/-- The Minkowski metric of `Lorentz.Vector d` in the `(-,+,+,+)` convention, the negative of
Physlib's `+---` product `⟪·, ·⟫ₘ`. -/
def minkowskiBilin (d : ℕ) : LinearMap.BilinForm ℝ (Lorentz.Vector d) :=
  LinearMap.mk₂ ℝ (fun p q => -⟪p, q⟫ₘ)
    (fun p r q => by simp [_root_.add_comm])
    (fun c p q => by simp)
    (fun p q r => by simp [_root_.add_comm])
    (fun c p q => by simp)

open Lorentz Vector in
/-- The Minkowski metric in the `(-,+,+,+)` convention is Lorentzian. -/
lemma isLorentzian_minkowski (d : ℕ) : IsLorentzian (minkowskiBilin d) := by
  have hu : ⟪(basis (Sum.inl 0) : Vector d), basis (Sum.inl 0)⟫ₘ = 1 := by
    simp [minkowskiProduct_toCoord]
  refine ⟨fun v w => by simp [minkowskiBilin, minkowskiProduct_symm v w], basis (Sum.inl 0),
    by simp [minkowskiBilin, hu], fun v h hv => ?_⟩
  have hT : causalCharacter (basis (Sum.inl 0) : Vector d) = .timeLike :=
    (timeLike_iff_norm_sq_pos _).mpr (by rw [hu]; exact one_pos)
  have := minkowskiProduct_self_neg_of_timeLike_orthogonal hT hv
    (by simpa [minkowskiBilin] using h)
  simpa [minkowskiBilin] using this

end GeneralRelativity
