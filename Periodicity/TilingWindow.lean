import Mathlib.Analysis.Complex.Norm
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Cutoff estimates for the tiling window

The inputs are the packing identities and the two loss bounds from the
paper. The conclusion is the two-sided estimate with the same constants
as in the proof of the Riesz window.
-/

namespace Periodicity

open MeasureTheory

private theorem norm_sub_sq_le (V W : ℂ) (η : ℝ) (hη : 0 < η) :
    ‖W - V‖^2 ≤ (1 + η) * ‖V‖^2 + (1 + η⁻¹) * ‖W‖^2 := by
  have hsq := sq_nonneg (η * ‖V‖ - ‖W‖)
  have htriangle : ‖W - V‖^2 ≤ (‖W‖ + ‖V‖)^2 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le _ _) _
  have hinv : η⁻¹ * η = 1 := inv_mul_cancel₀ (ne_of_gt hη)
  have hscaled : η * (‖W‖ + ‖V‖)^2 ≤
      η * ((1 + η) * ‖V‖^2 + (1 + η⁻¹) * ‖W‖^2) := by
    calc
      η * (‖W‖ + ‖V‖)^2 ≤ η * ((1 + η) * ‖V‖^2) + (η + 1) * ‖W‖^2 := by
        nlinarith
      _ = η * ((1 + η) * ‖V‖^2 + (1 + η⁻¹) * ‖W‖^2) := by
        calc
          _ = η * ((1 + η) * ‖V‖^2) + (η + η⁻¹ * η) * ‖W‖^2 := by rw [hinv]
          _ = _ := by ring
  exact htriangle.trans (le_of_mul_le_mul_left hscaled hη)

/-- Integrated cutoff loss. Here w represents the squared exponential sum. -/
theorem tilingCutoffLoss {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (U V W : α → ℂ) (θ ψ w : α → ℝ) (η δ : ℝ) (hη : 0 < η)
    (hU : ∀ t, U t = W t - V t)
    (hθ : ∀ t, 0 ≤ θ t ∧ θ t ≤ 1)
    (hψ : ∀ t, 0 ≤ ψ t ∧ ψ t ≤ 1)
    (hw : ∀ t, 0 ≤ w t)
    (hsmall : ∀ t, θ t * (1 - ψ t) ≠ 0 → ‖W t‖ ≤ δ)
    (hiLoss : Integrable (fun t ↦ θ t * (1 - ψ t) * (‖U t‖^2 * w t)) μ)
    (hiV : Integrable (fun t ↦ ‖V t‖^2 * w t) μ)
    (hiMass : Integrable (fun t ↦ θ t * (1 - ψ t) * w t) μ) :
    (∫ t, θ t * (1 - ψ t) * (‖U t‖^2 * w t) ∂μ) ≤
      (1 + η) * (∫ t, ‖V t‖^2 * w t ∂μ) +
      ((1 + η⁻¹) * δ^2) * (∫ t, θ t * (1 - ψ t) * w t ∂μ) := by
  let c t := θ t * (1 - ψ t)
  have hc (t : α) : 0 ≤ c t ∧ c t ≤ 1 := by
    have h : 0 ≤ 1 - ψ t := sub_nonneg.mpr (hψ t).2
    refine ⟨mul_nonneg (hθ t).1 h, ?_⟩
    calc
      c t ≤ 1 * (1 - ψ t) := mul_le_mul_of_nonneg_right (hθ t).2 h
      _ ≤ 1 := by linarith [(hψ t).1]
  have hηinv : 0 ≤ 1 + η⁻¹ := by positivity
  have hpoint (t : α) :
      c t * (‖U t‖^2 * w t) ≤
        (1 + η) * (‖V t‖^2 * w t) + ((1 + η⁻¹) * δ^2) * (c t * w t) := by
    have hv : 0 ≤ (1 + η) * ‖V t‖^2 := by positivity
    by_cases hz : c t = 0
    · simpa [hz, ← mul_assoc] using mul_nonneg hv (hw t)
    · have hd : ‖W t‖^2 ≤ δ^2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hsmall t hz) _
      have hnorm : ‖U t‖^2 ≤ (1 + η) * ‖V t‖^2 + (1 + η⁻¹) * δ^2 := by
        rw [hU]
        exact (norm_sub_sq_le (V t) (W t) η hη).trans
          (add_le_add le_rfl (mul_le_mul_of_nonneg_left hd hηinv))
      calc
        c t * (‖U t‖^2 * w t) ≤
            c t * (((1 + η) * ‖V t‖^2 + (1 + η⁻¹) * δ^2) * w t) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hnorm (hw t)) (hc t).1
        _ = (c t * ((1 + η) * ‖V t‖^2)) * w t + ((1 + η⁻¹) * δ^2) * (c t * w t) := by
          ring
        _ ≤ _ := by
          rw [← mul_assoc (1 + η)]
          exact add_le_add
            (mul_le_mul_of_nonneg_right (by simpa using mul_le_mul_of_nonneg_right (hc t).2 hv)
              (hw t)) le_rfl
  let f (t : α) := (1 + η) * (‖V t‖^2 * w t)
  let g (t : α) := ((1 + η⁻¹) * δ^2) * (c t * w t)
  have hf : Integrable f μ := hiV.const_mul _
  have hg : Integrable g μ := hiMass.const_mul _
  calc
    _ ≤ ∫ t, f t + g t ∂μ := integral_mono hiLoss (hf.add hg) hpoint
    _ = _ := by rw [integral_add hf hg]; simp [f, g, c, integral_const_mul]

/-- Two-sided Riesz window estimate from the packing identities and cutoff bounds. -/
theorem tilingWindowBounds {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (U V W : α → ℂ) (θ ψ w : α → ℝ) (η δ k e Q C : ℝ)
    (hη : 0 < η) (hQ : 0 ≤ Q)
    (hU : ∀ t, U t = W t - V t)
    (hθ : ∀ t, 0 ≤ θ t ∧ θ t ≤ 1)
    (hψ : ∀ t, 0 ≤ ψ t ∧ ψ t ≤ 1)
    (hw : ∀ t, 0 ≤ w t)
    (hsmall : ∀ t, θ t * (1 - ψ t) ≠ 0 → ‖W t‖ ≤ δ)
    (hiU : Integrable (fun t ↦ ‖U t‖^2 * w t) μ)
    (hiV : Integrable (fun t ↦ ‖V t‖^2 * w t) μ)
    (hiTail : Integrable (fun t ↦ (1 - θ t) * (‖U t‖^2 * w t)) μ)
    (hiLoss : Integrable (fun t ↦ θ t * (1 - ψ t) * (‖U t‖^2 * w t)) μ)
    (hiMass : Integrable (fun t ↦ θ t * (1 - ψ t) * w t) μ)
    (hiWin : Integrable (fun t ↦ θ t * ψ t * (‖U t‖^2 * w t)) μ)
    (hpackingU : (∫ t, ‖U t‖^2 * w t ∂μ) = k * Q)
    (hpackingV : (∫ t, ‖V t‖^2 * w t ∂μ) = e * Q)
    (hTail : (∫ t, (1 - θ t) * (‖U t‖^2 * w t) ∂μ) ≤ (k - (1 + η) * e) / 4 * Q)
    (hMass : (∫ t, θ t * (1 - ψ t) * w t ∂μ) ≤ C * Q)
    (hError : (1 + η⁻¹) * δ^2 * C ≤ (k - (1 + η) * e) / 4) :
    (k - (1 + η) * e) / 2 * Q ≤ (∫ t, θ t * ψ t * (‖U t‖^2 * w t) ∂μ) ∧
      (∫ t, θ t * ψ t * (‖U t‖^2 * w t) ∂μ) ≤ k * Q := by
  have hsplit :
      (∫ t, ‖U t‖^2 * w t ∂μ) =
        (∫ t, θ t * ψ t * (‖U t‖^2 * w t) ∂μ) +
          (∫ t, (1 - θ t) * (‖U t‖^2 * w t) ∂μ) +
          (∫ t, θ t * (1 - ψ t) * (‖U t‖^2 * w t) ∂μ) := by
    calc
      _ = ∫ t, (θ t * ψ t * (‖U t‖^2 * w t) +
          (1 - θ t) * (‖U t‖^2 * w t)) + θ t * (1 - ψ t) * (‖U t‖^2 * w t) ∂μ := by
        congr 1
        funext t
        ring
      _ = _ := by rw [integral_add (by exact hiWin.add hiTail) hiLoss, integral_add hiWin hiTail]
  have hLoss := tilingCutoffLoss μ U V W θ ψ w η δ hη hU hθ hψ hw hsmall
    hiLoss hiV hiMass
  have hcoeff : 0 ≤ (1 + η⁻¹) * δ^2 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hMass hcoeff
  have herr := mul_le_mul_of_nonneg_right hError hQ
  rw [hpackingU] at hsplit
  rw [hpackingV] at hLoss
  refine ⟨?_, ?_⟩
  · linarith only [hsplit, hTail, hLoss, hmul, herr]
  · rw [← hpackingU]
    refine integral_mono hiWin hiU fun t ↦ ?_
    have hprod : θ t * ψ t ≤ 1 := by
      calc
        θ t * ψ t ≤ 1 * ψ t := mul_le_mul_of_nonneg_right (hθ t).2 (hψ t).1
        _ ≤ 1 := by simpa using (hψ t).2
    simpa using mul_le_mul_of_nonneg_right hprod
      (mul_nonneg (sq_nonneg ‖U t‖) (hw t))

end Periodicity
