/-
Copyright (c) 2026 Harsha Vankayalapati. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harsha Vankayalapati
-/
module

public import PhyslibAlpha.Relativity.General.ChronologyRelations
public import PhyslibAlpha.Relativity.General.EnergyConditions
public import PhyslibAlpha.Relativity.General.Godel.ClosedTimelikeCurve
public import PhyslibAlpha.Relativity.General.Godel.Einstein

/-!

# The hypotheses of Hawking's chronology protection theorem

Definitions of the objects occurring in Hawking's theorem that a compactly generated Cauchy
horizon cannot exist when the weak energy condition holds.

## i. Overview

Hawking's theorem concerns a spacetime in which causality violation develops from an achronal
set `S`. Its hypotheses are: the future Cauchy horizon `H⁺(S)` is non-empty and compactly
generated (its past-directed null generators enter and remain in a compact set), and the stress
energy tensor satisfies the weak energy condition. The conclusion is that these are
incompatible.

This file states the hypotheses for a coordinate spacetime `(U, g)` with a time orientation `X`
(as in `ChronologyRelations`), as definitions only. The statement of the theorem itself is the
proposition `HawkingChronologyProtectionStatement`; it is not proved, since the proof needs the
Raychaudhuri equation for null congruences, the structure theory of Cauchy horizons and a
compactness argument, none of which are available yet.

The cases of interest, such as the Gödel universe, have a periodic coordinate. Since the
definitions here are for the covering coordinates, a chronology violation modulo a period `τ` is
captured by `chronologyViolatingSetMod`, and the Gödel universe is shown to violate chronology in
this sense while satisfying the weak energy condition for its dust.

## ii. Key results

- `SatisfiesWeakEnergyConditionOn`, `SatisfiesNullEnergyConditionOn` : the energy conditions for
  a stress energy field.
- `IsAchronal` : a set no two points of which are chronologically related.
- `IsFutureCausalCurveOnInterval`, `HasPastEndpoint`, `IsNullGeodesicOnInterval` : curves on
  arbitrary intervals, needed for inextendible curves and generators.
- `futureDomainOfDependence`, `futureCauchyHorizon` : `D⁺(S)` and `H⁺(S)`.
- `IsHorizonGenerator`, `IsCompactlyGenerated` : the null generators of `H⁺(S)` and the compact
  generation condition.
- `HawkingHypotheses`, `HawkingChronologyProtectionStatement` : the hypotheses and the statement
  of the theorem.
- `chronologyViolatingSetMod` : chronology violation modulo a period.
- `godelCircle_mem_chronologyViolatingSetMod` : the Gödel universe violates chronology.
- `satisfiesWeakEnergyConditionOn_godelStressEnergy` : the Gödel dust satisfies the weak energy
  condition.

## iii. Table of contents

- A. Energy conditions for a stress energy field
- B. Achronal sets and chronological pasts of sets
- C. Inextendible curves and the domain of dependence
- D. The Cauchy horizon and its generators
- E. The statement of Hawking's theorem
- F. Chronology violation modulo a period
- G. The Gödel universe

## iv. References

- S. W. Hawking, *The chronology protection conjecture*, Phys. Rev. D 46, 603 (1992).
- S. W. Hawking and G. F. R. Ellis, *The Large Scale Structure of Space-Time*, Sections 6.4
  and 6.5.

-/

@[expose] public section

noncomputable section

namespace GeneralRelativity

open Set Topology Real

variable {g T : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ} {X : (Fin 4 → ℝ) → Fin 4 → ℝ}
  {U S : Set (Fin 4 → ℝ)}

/-!

## A. Energy conditions for a stress energy field

-/

/-- The stress energy field `T` satisfies the weak energy condition on `U` for the metric `g`. -/
def SatisfiesWeakEnergyConditionOn (g T : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ)
    (U : Set (Fin 4 → ℝ)) : Prop :=
  ∀ x ∈ U, WeakEnergyCondition (Matrix.toBilin' (g x)) (Matrix.toBilin' (T x))

/-- The stress energy field `T` satisfies the null energy condition on `U` for the metric `g`. -/
def SatisfiesNullEnergyConditionOn (g T : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ)
    (U : Set (Fin 4 → ℝ)) : Prop :=
  ∀ x ∈ U, NullEnergyCondition (Matrix.toBilin' (g x)) (Matrix.toBilin' (T x))

/-- The weak energy condition implies the null energy condition on `U`. -/
lemma SatisfiesWeakEnergyConditionOn.satisfiesNullEnergyConditionOn
    (hg : IsLorentzianMetricOn g U) (h : SatisfiesWeakEnergyConditionOn g T U) :
    SatisfiesNullEnergyConditionOn g T U :=
  fun x hx => (h x hx).nullEnergyCondition (hg.lorentzian x hx)

/-!

## B. Achronal sets and chronological pasts of sets

-/

/-- A set `S` is achronal if no point of `S` lies in the chronological future of another. -/
def IsAchronal (g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ) (X : (Fin 4 → ℝ) → Fin 4 → ℝ)
    (U : Set (Fin 4 → ℝ)) (S : Set (Fin 4 → ℝ)) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, q ∉ chronologicalFuture g X U p

/-- The chronological past `I⁻(A)` of a set `A`: the points whose chronological future meets
`A`. -/
def chronologicalPastOfSet (g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ)
    (X : (Fin 4 → ℝ) → Fin 4 → ℝ) (U : Set (Fin 4 → ℝ)) (A : Set (Fin 4 → ℝ)) :
    Set (Fin 4 → ℝ) :=
  {q | ∃ a ∈ A, a ∈ chronologicalFuture g X U q}

/-- A single point is achronal exactly when it is not chronology violating. -/
lemma isAchronal_singleton_iff {p : Fin 4 → ℝ} :
    IsAchronal g X U {p} ↔ p ∉ chronologyViolatingSet g X U := by
  simp [IsAchronal, chronologyViolatingSet]

/-- A subset of an achronal set is achronal. -/
lemma IsAchronal.mono {S' : Set (Fin 4 → ℝ)} (h : IsAchronal g X U S) (hS : S' ⊆ S) :
    IsAchronal g X U S' :=
  fun p hp q hq => h p (hS hp) q (hS hq)

/-!

## C. Inextendible curves and the domain of dependence

-/

/-- A future-directed causal curve on an interval `I`: `I` is a non-trivial interval, `γ` is `C¹`
on it and stays in `U`, and its tangent is causal with `g (X (γ t)) (γ' t) < 0`. -/
def IsFutureCausalCurveOnInterval (g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ)
    (X : (Fin 4 → ℝ) → Fin 4 → ℝ) (U : Set (Fin 4 → ℝ)) (γ : ℝ → Fin 4 → ℝ) (I : Set ℝ) :
    Prop :=
  I.OrdConnected ∧ I.Nontrivial ∧ ContDiffOn ℝ 1 γ I ∧ (∀ t ∈ I, γ t ∈ U) ∧
    ∀ t ∈ I, IsCausal (Matrix.toBilin' (g (γ t))) (derivWithin γ I t) ∧
      Matrix.toBilin' (g (γ t)) (X (γ t)) (derivWithin γ I t) < 0

/-- The curve `γ` on `I` has a past endpoint in `U`: a point `q ∈ U` which `γ t` approaches as
`t` decreases through `I`. If `I` has a least element, its image is a past endpoint. -/
def HasPastEndpoint (U : Set (Fin 4 → ℝ)) (γ : ℝ → Fin 4 → ℝ) (I : Set ℝ) : Prop :=
  ∃ q ∈ U, ∀ N ∈ 𝓝 q, ∃ t ∈ I, ∀ s ∈ I, s ≤ t → γ s ∈ N

/-- `γ` on `I` is a past-inextendible future-directed causal curve ending at `p`: `p` is the
image of the last parameter of `I`, and `γ` has no past endpoint. -/
structure IsPastInextendibleCurveEndingAt (g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ)
    (X : (Fin 4 → ℝ) → Fin 4 → ℝ) (U : Set (Fin 4 → ℝ)) (p : Fin 4 → ℝ)
    (γ : ℝ → Fin 4 → ℝ) (I : Set ℝ) : Prop where
  /-- `γ` is a future-directed causal curve. -/
  curve : IsFutureCausalCurveOnInterval g X U γ I
  /-- `γ` has no past endpoint. -/
  noPastEndpoint : ¬ HasPastEndpoint U γ I
  /-- `p` is the point at the last parameter of `γ`. -/
  ending : ∃ t ∈ I, γ t = p ∧ ∀ s ∈ I, s ≤ t

/-- The future domain of dependence `D⁺(S)`: the points `p ∈ U` such that every past-inextendible
causal curve ending at `p` meets `S`. -/
def futureDomainOfDependence (g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ)
    (X : (Fin 4 → ℝ) → Fin 4 → ℝ) (U : Set (Fin 4 → ℝ)) (S : Set (Fin 4 → ℝ)) :
    Set (Fin 4 → ℝ) :=
  {p ∈ U | ∀ (γ : ℝ → Fin 4 → ℝ) (I : Set ℝ),
    IsPastInextendibleCurveEndingAt g X U p γ I → ∃ s ∈ I, γ s ∈ S}

/-- A subset `S ⊆ U` lies in its own future domain of dependence. -/
lemma subset_futureDomainOfDependence (hS : S ⊆ U) : S ⊆ futureDomainOfDependence g X U S := by
  intro p hp
  refine ⟨hS hp, fun γ I h => ?_⟩
  obtain ⟨t, ht, hγ, -⟩ := h.ending
  exact ⟨t, ht, by rw [hγ]; exact hp⟩

/-!

## D. The Cauchy horizon and its generators

-/

/-- The future Cauchy horizon `H⁺(S) = closure D⁺(S) \ I⁻(D⁺(S))`, taken inside `U`. -/
def futureCauchyHorizon (g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ)
    (X : (Fin 4 → ℝ) → Fin 4 → ℝ) (U : Set (Fin 4 → ℝ)) (S : Set (Fin 4 → ℝ)) :
    Set (Fin 4 → ℝ) :=
  (closure (futureDomainOfDependence g X U S) ∩ U) \
    chronologicalPastOfSet g X U (futureDomainOfDependence g X U S)

/-- The future Cauchy horizon lies in the closure of the domain of dependence. -/
lemma futureCauchyHorizon_subset_closure :
    futureCauchyHorizon g X U S ⊆ closure (futureDomainOfDependence g X U S) :=
  fun _ h => h.1.1

/-- The future Cauchy horizon is disjoint from the chronological past of the domain of
dependence. -/
lemma disjoint_futureCauchyHorizon_chronologicalPastOfSet :
    Disjoint (futureCauchyHorizon g X U S)
      (chronologicalPastOfSet g X U (futureDomainOfDependence g X U S)) :=
  Set.disjoint_left.2 fun _ h => h.2

/-- A curve `γ` on `I` is a null geodesic: it is `C²` and satisfies the geodesic equation
`γ''^a + Γ^a_{bc} γ'^b γ'^c = 0` with null tangent. -/
def IsNullGeodesicOnInterval (g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ) (γ : ℝ → Fin 4 → ℝ)
    (I : Set ℝ) : Prop :=
  ContDiffOn ℝ 2 γ I ∧ ∀ t ∈ I,
    IsNull (Matrix.toBilin' (g (γ t))) (derivWithin γ I t) ∧
    ∀ a, derivWithin (derivWithin γ I) I t a + ∑ b, ∑ c,
      christoffel g (γ t) a b c * derivWithin γ I t b * derivWithin γ I t c = 0

/-- A null generator of `H⁺(S)`: a future-directed null geodesic lying in `H⁺(S)` and having no
past endpoint in `U`. -/
structure IsHorizonGenerator (g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ)
    (X : (Fin 4 → ℝ) → Fin 4 → ℝ) (U S : Set (Fin 4 → ℝ)) (γ : ℝ → Fin 4 → ℝ) (I : Set ℝ) :
    Prop where
  /-- `γ` is a future-directed causal curve. -/
  curve : IsFutureCausalCurveOnInterval g X U γ I
  /-- `γ` is a null geodesic. -/
  geodesic : IsNullGeodesicOnInterval g γ I
  /-- `γ` lies in the Cauchy horizon. -/
  mem : ∀ t ∈ I, γ t ∈ futureCauchyHorizon g X U S
  /-- `γ` has no past endpoint. -/
  noPastEndpoint : ¬ HasPastEndpoint U γ I

/-- `H⁺(S)` is compactly generated: there is a compact `K ⊆ U` such that every null generator,
followed into the past, enters `K` and remains in it. -/
def IsCompactlyGenerated (g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ)
    (X : (Fin 4 → ℝ) → Fin 4 → ℝ) (U S : Set (Fin 4 → ℝ)) : Prop :=
  ∃ K : Set (Fin 4 → ℝ), IsCompact K ∧ K ⊆ U ∧ ∀ (γ : ℝ → Fin 4 → ℝ) (I : Set ℝ),
    IsHorizonGenerator g X U S γ I → ∃ t₀ ∈ I, ∀ t ∈ I, t ≤ t₀ → γ t ∈ K

/-- Compact generation holds vacuously when there are no generators, which is why Hawking's
hypotheses also require `H⁺(S)` to be non-empty. -/
lemma isCompactlyGenerated_of_forall_not_isHorizonGenerator
    (h : ∀ (γ : ℝ → Fin 4 → ℝ) (I : Set ℝ), ¬ IsHorizonGenerator g X U S γ I) :
    IsCompactlyGenerated g X U S :=
  ⟨∅, isCompact_empty, empty_subset _, fun γ I hγ => absurd hγ (h γ I)⟩

/-!

## E. The statement of Hawking's theorem

-/

/-- The hypotheses of Hawking's theorem for a stress energy field `T`, a time orientation `X`
and an achronal set `S ⊆ U`: Einstein's equations without cosmological constant, the weak energy
condition, and a non-empty compactly generated future Cauchy horizon. -/
structure HawkingHypotheses (g T : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ)
    (X : (Fin 4 → ℝ) → Fin 4 → ℝ) (U S : Set (Fin 4 → ℝ)) : Prop where
  /-- The metric is Lorentzian on `U`. -/
  lorentzian : IsLorentzianMetricOn g U
  /-- `X` is a time orientation. -/
  timeOrientation : IsTimeOrientationOn g U X
  /-- Einstein's equations `G_{ab} = T_{ab}`. -/
  einstein : ∀ x ∈ U, ∀ a b, GeneralRelativity.einstein g x a b = T x a b
  /-- The weak energy condition. -/
  weakEnergy : SatisfiesWeakEnergyConditionOn g T U
  /-- `S` lies in `U`. -/
  subset : S ⊆ U
  /-- `S` is achronal. -/
  achronal : IsAchronal g X U S
  /-- The future Cauchy horizon is non-empty. -/
  nonempty : (futureCauchyHorizon g X U S).Nonempty
  /-- The future Cauchy horizon is compactly generated. -/
  compactlyGenerated : IsCompactlyGenerated g X U S

/-- The statement of Hawking's theorem: the hypotheses `HawkingHypotheses` are inconsistent.
This is a proposition, not a proved result. -/
def HawkingChronologyProtectionStatement (g T : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ)
    (X : (Fin 4 → ℝ) → Fin 4 → ℝ) (U S : Set (Fin 4 → ℝ)) : Prop :=
  HawkingHypotheses g T X U S → False

/-!

## F. Chronology violation modulo a period

-/

/-- `q` is reached from `p` by one future-directed timelike segment, modulo the period `τ`: the
segment ends at `q + k τ` for some integer `k`. -/
def IsFutureTimelikeStepMod (g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ)
    (X : (Fin 4 → ℝ) → Fin 4 → ℝ) (U : Set (Fin 4 → ℝ)) (τ : Fin 4 → ℝ) (p q : Fin 4 → ℝ) :
    Prop :=
  ∃ k : ℤ, IsFutureTimelikeStep g X U p (q + k • τ)

/-- The points `p` of the spacetime obtained by identifying points differing by `τ` which lie in
their own chronological future. -/
def chronologyViolatingSetMod (g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ)
    (X : (Fin 4 → ℝ) → Fin 4 → ℝ) (U : Set (Fin 4 → ℝ)) (τ : Fin 4 → ℝ) : Set (Fin 4 → ℝ) :=
  {p | Relation.TransGen (IsFutureTimelikeStepMod g X U τ) p p}

/-- With the trivial period, chronology violation modulo the period is chronology violation. -/
lemma chronologyViolatingSetMod_zero :
    chronologyViolatingSetMod g X U 0 = chronologyViolatingSet g X U := by
  have h : IsFutureTimelikeStepMod g X U 0 = IsFutureTimelikeStep g X U := by
    funext p q
    simp [IsFutureTimelikeStepMod]
  simp [chronologyViolatingSetMod, chronologyViolatingSet, chronologicalFuture, h]

/-- A future-directed timelike curve with `γ b = γ a + τ` shows that `γ a` violates chronology
modulo `τ`. -/
lemma mem_chronologyViolatingSetMod_of_loop {τ : Fin 4 → ℝ} {γ : ℝ → Fin 4 → ℝ} {a b : ℝ}
    (h : IsFutureTimelikeCurveOn g X U γ a b) (hτ : γ b = γ a + τ) :
    γ a ∈ chronologyViolatingSetMod g X U τ :=
  Relation.TransGen.single ⟨1, γ, a, b, h, rfl, by simpa using hτ⟩

/-!

## G. The Gödel universe

-/

/-- The time orientation of the Gödel universe: the vector field `∂_t`. -/
def godelTimeField : (Fin 4 → ℝ) → Fin 4 → ℝ := fun _ => Pi.single 0 1

/-- `∂_t` is a time orientation of the Gödel universe. -/
lemma isTimeOrientationOn_godelTimeField : IsTimeOrientationOn godelMetric godelDomain
    godelTimeField where
  continuousOn := continuousOn_const
  isTimelike x _ := by simp [IsTimelike, godelTimeField, godelMetric, godelMetricR]

/-- Beyond the critical radius the circle of the Gödel universe is a future-directed timelike
curve. -/
lemma isFutureTimelikeCurveOn_godelCircle {t₀ r₀ z₀ : ℝ} (h : godelCriticalRadius < r₀) :
    IsFutureTimelikeCurveOn godelMetric godelTimeField godelDomain (godelCircle t₀ r₀ z₀) 0
      (2 * π) := by
  refine ⟨(isTimelikeLoopMod_godelCircle h).1, fun s hs => ?_⟩
  have hu : UniqueDiffWithinAt ℝ (Icc 0 (2 * π)) s := uniqueDiffOn_Icc (by positivity) s hs
  rw [(hasDerivAt_godelCircle t₀ r₀ z₀ s).hasDerivWithinAt.derivWithin hu]
  have hr : 0 < r₀ := godelCriticalRadius_pos.trans h
  simp only [godelMetric_bilin, godelTimeField, godelCircle]
  simp
  positivity

/-- The Gödel universe violates chronology: a point on a circle beyond the critical radius lies
in its own chronological future, modulo the angular period. -/
lemma godelCircle_mem_chronologyViolatingSetMod {t₀ r₀ z₀ : ℝ} (h : godelCriticalRadius < r₀) :
    godelCircle t₀ r₀ z₀ 0 ∈
      chronologyViolatingSetMod godelMetric godelTimeField godelDomain godelPeriod :=
  mem_chronologyViolatingSetMod_of_loop (isFutureTimelikeCurveOn_godelCircle h)
    (isTimelikeLoopMod_godelCircle h).2

/-- The chronology violating set of the Gödel universe is non-empty. -/
lemma godel_chronologyViolatingSetMod_nonempty :
    (chronologyViolatingSetMod godelMetric godelTimeField godelDomain godelPeriod).Nonempty :=
  ⟨_, godelCircle_mem_chronologyViolatingSetMod
    (t₀ := 0) (r₀ := godelCriticalRadius + 1) (z₀ := 0) (by linarith)⟩

/-- The stress energy of the dust of the Gödel universe, `T_{ab} = ρ u_a u_b`. -/
def godelStressEnergy : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ := fun y =>
  Matrix.of fun a b => godelDensity * godelVelocityLower y a * godelVelocityLower y b

/-- The dust of the Gödel universe satisfies the weak energy condition. So the weak energy
condition alone does not prevent chronology violation, and the compact generation hypothesis of
Hawking's theorem is essential. -/
lemma satisfiesWeakEnergyConditionOn_godelStressEnergy :
    SatisfiesWeakEnergyConditionOn godelMetric godelStressEnergy godelDomain := by
  intro x _ v _
  have h : Matrix.toBilin' (godelStressEnergy x) v v
      = godelDensity * (∑ a, godelVelocityLower x a * v a) ^ 2 := by
    simp only [Matrix.toBilin'_apply', godelStressEnergy, dotProduct, Matrix.mulVec,
      Matrix.of_apply, Fin.sum_univ_four]
    ring
  rw [h]
  have : 0 ≤ godelDensity := by norm_num [godelDensity]
  positivity

end GeneralRelativity
