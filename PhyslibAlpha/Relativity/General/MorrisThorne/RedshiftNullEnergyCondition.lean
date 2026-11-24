/-
Copyright (c) 2026 Harsha Vankayalapati. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harsha Vankayalapati
-/
module

public import PhyslibAlpha.Relativity.General.MorrisThorne.NullEnergyCondition
public import PhyslibAlpha.Relativity.General.MorrisThorne.RedshiftRicci

/-!

# A traversable wormhole violates the null energy condition at its throat

For a static, spherically symmetric Morris-Thorne wormhole with any smooth redshift function `Φ`,
the flaring-out condition at the throat forces a violation of the null energy condition.

## i. Overview

Consider the metric `-e^{2Φ(r)} dt² + (1 - b(r)/r)⁻¹ dr² + r² dΩ²` with smooth `Φ` and `b`
(`morrisThorneRedshiftMetric`), supported by the stress-energy tensor `T_{ab} = G_{ab} / (8 π)`
required by Einstein's equations (`requiredStressEnergy`). A *throat* is a radius `r₀ > 0` with
`b(r₀) = r₀`, and *flaring out* is `b'(r₀) < 1`. The redshift function is finite at the throat
because it is smooth.

For the radial null vector `k = ∂_t + e^{Φ} √(1 - b/r) ∂_r` (`morrisThorneRedshiftNull`), the
off-diagonal Ricci component vanishes and `g(k, k) = 0`, so the Einstein tensor on `k` equals
the Ricci tensor on `k`, which only involves `R_tt` and `R_rr`. This gives
`T(k, k) = e^{2Φ} (r b' - b + 2 r (r - b) Φ') / (8 π r³)`
(`requiredStressEnergy_morrisThorneRedshift_null`). In the orthonormal frame of the static
observers this is `e^{2Φ} (ρ + p_r)`, since `k = e^{Φ} (ê_t + ê_r)`.

As `r → r₀` from outside, the term `2 r (r - b) Φ'` tends to zero because `b(r₀) = r₀` and `Φ'` is
finite, so `(r b' - b + 2 r (r - b) Φ') / (8 π r³) → (b'(r₀) - 1) / (8 π r₀²) < 0`
(`tendsto_redshiftNullFlux_throat`), independent of `Φ`. Hence the null energy condition fails
at every point of the region just outside a flared-out throat
(`not_nullEnergyCondition_morrisThorneRedshift_near_throat`): a traversable static spherically
symmetric wormhole requires matter violating the null energy condition at its throat.

The coordinate `r` is singular at the throat itself (`g_rr` diverges), so the statement is about
the points arbitrarily close to the throat, as for `Φ = 0`.

## ii. Key results

- `requiredStressEnergy_morrisThorneRedshift_null` : `T(k, k)` for the radial null vector `k`.
- `not_nullEnergyCondition_morrisThorneRedshift` : the null energy condition fails where
  `r b' - b + 2 r (r - b) Φ' < 0`.
- `tendsto_redshiftNullFlux_throat` : the limit of the null flux at the throat is negative.
- `not_nullEnergyCondition_morrisThorneRedshift_near_throat` : the no-go theorem.

## iii. Table of contents

- A. A null vector and the stress-energy tensor on it
- B. Violation of the null energy condition
- C. The throat

## iv. References

- M. S. Morris and K. S. Thorne, *Wormholes in spacetime and their use for interstellar travel:
  A tool for teaching general relativity*, Am. J. Phys. 56, 395 (1988).
- M. Visser, *Lorentzian Wormholes: From Einstein to Hawking*, AIP Press (1995), Chapter 11.

-/

@[expose] public section

noncomputable section

namespace GeneralRelativity

open Real Filter Topology
open scoped ContDiff

/-!

## A. A null vector and the stress-energy tensor on it

-/

/-- The radially outgoing null vector `∂_t + e^{Φ} √(1 - b/r) ∂_r`. -/
def morrisThorneRedshiftNull (Φ b : ℝ → ℝ) (x : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![1, exp (Φ (x 1)) * √(1 - b (x 1) / x 1), 0, 0]

/-- The combination `(r b' - b + 2 r (r - b) Φ') / (8 π r³)`, equal to `ρ + p_r` of the matter
required by a Morris-Thorne wormhole with redshift function `Φ` in the orthonormal frame of the
static observers. -/
def redshiftNullFlux (Φ b : ℝ → ℝ) (r : ℝ) : ℝ :=
  (r * deriv b r - b r + 2 * r * (r - b r) * deriv Φ r) / (8 * π * r ^ 3)

section NullVector

variable {Φ b : ℝ → ℝ} {x : Fin 4 → ℝ}

lemma morrisThorneRedshiftNull_one_mul_self (hx : x ∈ morrisThorneDomain b) :
    (exp (Φ (x 1)) * √(1 - b (x 1) / x 1)) * (exp (Φ (x 1)) * √(1 - b (x 1) / x 1))
      = exp (2 * Φ (x 1)) * (1 - b (x 1) / x 1) := by
  have hs := Real.mul_self_sqrt (morrisThorneDomain.one_sub_pos hx).le
  have he : exp (2 * Φ (x 1)) = exp (Φ (x 1)) * exp (Φ (x 1)) := by
    rw [← exp_add]; ring_nf
  calc _ = (exp (Φ (x 1)) * exp (Φ (x 1))) * (√(1 - b (x 1) / x 1) * √(1 - b (x 1) / x 1)) := by
        ring
    _ = _ := by rw [hs, he]

lemma isNull_morrisThorneRedshiftNull (hx : x ∈ morrisThorneDomain b) :
    IsNull (Matrix.toBilin' (morrisThorneRedshiftMetric Φ b x))
      (morrisThorneRedshiftNull Φ b x) := by
  have h2 := (morrisThorneDomain.one_sub_pos hx)
  refine ⟨?_, fun h => ?_⟩
  · rw [morrisThorneRedshiftMetric, toBilin'_diagonal_four]
    simp only [Fin.isValue, Matrix.cons_val_zero, morrisThorneRedshiftNull, mul_one,
      Matrix.cons_val_one, Matrix.cons_val, mul_zero, add_zero]
    rw [morrisThorneRedshiftNull_one_mul_self hx]
    field_simp
    ring
  · have := congrFun h 0
    simp [morrisThorneRedshiftNull] at this

/-- The stress-energy tensor required by a Morris-Thorne wormhole with redshift function `Φ`,
evaluated on the null vector `morrisThorneRedshiftNull`, is `e^{2Φ} (ρ + p_r)`. -/
lemma requiredStressEnergy_morrisThorneRedshift_null (hΦ : ContDiff ℝ ∞ Φ) (hb : ContDiff ℝ ∞ b)
    (hx : x ∈ morrisThorneDomain b) :
    Matrix.toBilin' (requiredStressEnergy (morrisThorneRedshiftMetric Φ b) x)
      (morrisThorneRedshiftNull Φ b x) (morrisThorneRedshiftNull Φ b x)
      = exp (2 * Φ (x 1)) * redshiftNullFlux Φ b (x 1) := by
  have h1 := (morrisThorneDomain.pos hx).ne'
  have h2 := (morrisThorneDomain.one_sub_pos hx)
  have h3 := (morrisThorneDomain.sub_pos hx).ne'
  have hsym := ricci_symm (isLorentzianMetricOn_morrisThorneRedshiftMetric hΦ hb) hx 0 1
  have hf := morrisThorneRedshiftNull_one_mul_self (Φ := Φ) hx
  simp [Matrix.toBilin'_apply', dotProduct, Matrix.mulVec, Fin.sum_univ_four,
    requiredStressEnergy, einstein, Matrix.of_apply, morrisThorneRedshiftNull,
    morrisThorneRedshiftMetric, Matrix.diagonal_apply]
  rw [← hsym, ricci_morrisThorneRedshift_tr hΦ hb hx, ricci_morrisThorneRedshift_tt hΦ hb hx,
    ricci_morrisThorneRedshift_rr hΦ hb hx]
  have key : ∀ Y Z : ℝ, exp (Φ (x 1)) * √(1 - b (x 1) / x 1)
      * (Y + Z * (exp (Φ (x 1)) * √(1 - b (x 1) / x 1)))
      = exp (Φ (x 1)) * √(1 - b (x 1) / x 1) * Y
        + Z * (exp (2 * Φ (x 1)) * (1 - b (x 1) / x 1)) := fun Y Z => by
    rw [← hf]; ring
  simp only [key, redshiftNullFlux]
  have h4 := h2.ne'
  field_simp
  ring

end NullVector

/-!

## B. Violation of the null energy condition

-/

section Violation

variable {Φ b : ℝ → ℝ} {x : Fin 4 → ℝ}

/-- The null energy condition fails for the matter required by a Morris-Thorne wormhole with
redshift function `Φ` at every point where `r b' - b + 2 r (r - b) Φ' < 0`. -/
lemma not_nullEnergyCondition_morrisThorneRedshift (hΦ : ContDiff ℝ ∞ Φ) (hb : ContDiff ℝ ∞ b)
    (hx : x ∈ morrisThorneDomain b)
    (h : x 1 * deriv b (x 1) - b (x 1) + 2 * x 1 * (x 1 - b (x 1)) * deriv Φ (x 1) < 0) :
    ¬ NullEnergyCondition (Matrix.toBilin' (morrisThorneRedshiftMetric Φ b x))
      (Matrix.toBilin' (requiredStressEnergy (morrisThorneRedshiftMetric Φ b) x)) := by
  intro hnec
  have := hnec _ (isNull_morrisThorneRedshiftNull hx)
  rw [requiredStressEnergy_morrisThorneRedshift_null hΦ hb hx] at this
  have h1 := morrisThorneDomain.pos hx
  have : redshiftNullFlux Φ b (x 1) < 0 := div_neg_of_neg_of_pos h (by positivity)
  have := exp_pos (2 * Φ (x 1))
  nlinarith

end Violation

/-!

## C. The throat

-/

section Throat

variable {Φ b : ℝ → ℝ} {r₀ : ℝ}

/-- The limit of `ρ + p_r` at a flared-out throat is `(b'(r₀) - 1) / (8 π r₀²)`, independently of
the redshift function. -/
lemma tendsto_redshiftNullFlux_throat (hΦ : ContDiff ℝ ∞ Φ) (hb : ContDiff ℝ ∞ b)
    (hr₀ : 0 < r₀) (hthroat : b r₀ = r₀) :
    Tendsto (redshiftNullFlux Φ b) (𝓝[>] r₀) (𝓝 ((deriv b r₀ - 1) / (8 * π * r₀ ^ 2))) := by
  obtain ⟨-, hd'⟩ := contDiff_infty_iff_deriv.mp hb
  obtain ⟨-, hΦ'⟩ := contDiff_infty_iff_deriv.mp hΦ
  have hc : ContinuousAt (redshiftNullFlux Φ b) r₀ := by
    unfold redshiftNullFlux
    refine ContinuousAt.div ?_ (by fun_prop) (by positivity)
    exact (((continuous_id.mul hd'.continuous).sub hb.continuous).add
      ((continuous_const.mul continuous_id).mul (continuous_id.sub hb.continuous)
        |>.mul hΦ'.continuous)).continuousAt
  have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi r₀))
  convert this using 2
  simp only [redshiftNullFlux, hthroat]
  field_simp
  ring

/-- At a flared-out throat the quantity `r b' - b + 2 r (r - b) Φ'` is negative just outside the
throat. -/
lemma eventually_redshift_lt_nhdsGT_throat (hΦ : ContDiff ℝ ∞ Φ) (hb : ContDiff ℝ ∞ b)
    (hr₀ : 0 < r₀) (hthroat : b r₀ = r₀) (hflare : deriv b r₀ < 1) :
    ∀ᶠ r in 𝓝[>] r₀, r * deriv b r - b r + 2 * r * (r - b r) * deriv Φ r < 0 := by
  obtain ⟨-, hd'⟩ := contDiff_infty_iff_deriv.mp hb
  obtain ⟨-, hΦ'⟩ := contDiff_infty_iff_deriv.mp hΦ
  have hc : ContinuousAt (fun r => r * deriv b r - b r + 2 * r * (r - b r) * deriv Φ r) r₀ :=
    (((continuous_id.mul hd'.continuous).sub hb.continuous).add
      ((continuous_const.mul continuous_id).mul (continuous_id.sub hb.continuous)
        |>.mul hΦ'.continuous)).continuousAt
  have hneg : (fun r => r * deriv b r - b r + 2 * r * (r - b r) * deriv Φ r) r₀ < 0 := by
    simp only [hthroat, sub_self, mul_zero, zero_mul, add_zero]
    nlinarith
  exact (hc.eventually_lt continuousAt_const hneg).filter_mono
    (nhdsWithin_le_nhds (s := Set.Ioi r₀))

/-- **No-go theorem for traversable wormholes.** For a static, spherically symmetric
Morris-Thorne wormhole with smooth shape function `b` and smooth, hence finite, redshift function
`Φ`, a flared-out throat (`b(r₀) = r₀`, `b'(r₀) < 1`) forces the matter required by Einstein's
equations to violate the null energy condition: there is `ε > 0` such that every point of the
wormhole with `r₀ < r < r₀ + ε` lies in the region `b(r) < r` and the null energy condition fails
there. -/
theorem not_nullEnergyCondition_morrisThorneRedshift_near_throat (hΦ : ContDiff ℝ ∞ Φ)
    (hb : ContDiff ℝ ∞ b) (hr₀ : 0 < r₀) (hthroat : b r₀ = r₀) (hflare : deriv b r₀ < 1) :
    ∀ᶠ r in 𝓝[>] r₀, ∀ x : Fin 4 → ℝ, x 1 = r → 0 < x 2 → x 2 < π →
      x ∈ morrisThorneDomain b ∧
        ¬ NullEnergyCondition (Matrix.toBilin' (morrisThorneRedshiftMetric Φ b x))
          (Matrix.toBilin' (requiredStressEnergy (morrisThorneRedshiftMetric Φ b) x)) := by
  filter_upwards [eventually_lt_nhdsGT_throat hb hthroat hflare,
    eventually_redshift_lt_nhdsGT_throat hΦ hb hr₀ hthroat hflare, self_mem_nhdsWithin]
    with r hlt hneg hr
  intro x hx1 hx2 hx2'
  subst hx1
  have hmem : x ∈ morrisThorneDomain b := ⟨lt_trans hr₀ hr, hlt, hx2, hx2'⟩
  exact ⟨hmem, not_nullEnergyCondition_morrisThorneRedshift hΦ hb hmem hneg⟩

/-- The null energy condition cannot hold on any region `r₀ < r < r₀ + ε` just outside a
flared-out throat: arbitrarily close to the throat there is a point at which it fails. -/
lemma exists_not_nullEnergyCondition_morrisThorneRedshift (hΦ : ContDiff ℝ ∞ Φ)
    (hb : ContDiff ℝ ∞ b) (hr₀ : 0 < r₀) (hthroat : b r₀ = r₀) (hflare : deriv b r₀ < 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ x ∈ morrisThorneDomain b, x 1 ∈ Set.Ioo r₀ (r₀ + ε) ∧
      ¬ NullEnergyCondition (Matrix.toBilin' (morrisThorneRedshiftMetric Φ b x))
        (Matrix.toBilin' (requiredStressEnergy (morrisThorneRedshiftMetric Φ b) x)) := by
  obtain ⟨r, hr, hr'⟩ := ((not_nullEnergyCondition_morrisThorneRedshift_near_throat hΦ hb hr₀
    hthroat hflare).and (Ioo_mem_nhdsGT (by linarith : r₀ < r₀ + ε))).exists
  have h := hr (![0, r, π / 2, 0]) rfl (by simp [pi_pos]) (by simp [pi_pos])
  exact ⟨_, h.1, by simpa using hr', h.2⟩

end Throat

end GeneralRelativity
