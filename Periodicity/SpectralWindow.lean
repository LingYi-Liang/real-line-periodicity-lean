import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The Gram matrix estimate for the spectral window

The Fourier and Parseval arguments in the paper produce the diagonal and
row/column bounds used here. This file proves the ensuing finite quadratic
form estimate for arbitrary complex coefficients.
-/

namespace Periodicity

open scoped BigOperators

private theorem weighted_schur {ι : Type*} [Fintype ι]
    (b : ι → ι → ℝ) (x : ι → ℝ) (r : ℝ)
    (hb : ∀ i j, 0 ≤ b i j)
    (hrow : ∀ i, (∑ j, b i j) ≤ r)
    (hcol : ∀ j, (∑ i, b i j) ≤ r) :
    (∑ i, ∑ j, b i j * (x i * x j)) ≤ r * ∑ i, (x i)^2 := by
  have hleft : (∑ i, ∑ j, b i j * (x i)^2) ≤ r * ∑ i, (x i)^2 := by
    simp only [← Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ ↦
      mul_le_mul_of_nonneg_right (hrow i) (sq_nonneg _)
  have hright : (∑ i, ∑ j, b i j * (x j)^2) ≤ r * ∑ i, (x i)^2 := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ ↦
      mul_le_mul_of_nonneg_right (hcol j) (sq_nonneg _)
  have hyoung :
      (∑ i, ∑ j, b i j * (x i * x j)) ≤
        ((∑ i, ∑ j, b i j * (x i)^2) + (∑ i, ∑ j, b i j * (x j)^2)) / 2 := by
    simp only [← Finset.sum_add_distrib, div_eq_mul_inv, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    have h : x i * x j ≤ ((x i)^2 + (x j)^2) / 2 := by
      nlinarith [sq_nonneg (x i - x j)]
    calc
      b i j * (x i * x j) ≤ b i j * (((x i)^2 + (x j)^2) / 2) :=
        mul_le_mul_of_nonneg_left h (hb i j)
      _ = (b i j * (x i)^2 + b i j * (x j)^2) * (2 : ℝ)⁻¹ := by ring
  linarith

/-- The spectral window bounds for a finite restriction of the Gram matrix.
The row and column sums run over the restriction with the diagonal removed. -/
theorem spectralWindowBounds {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → ι → ℂ) (v : ι → ℂ) (k : ℝ)
    (hdiag : ∀ i, A i i = (k^2 : ℝ))
    (hrow : ∀ i, (∑ j, if i = j then 0 else ‖A i j‖) ≤ k - k^2)
    (hcol : ∀ j, (∑ i, if i = j then 0 else ‖A i j‖) ≤ k - k^2) :
    (2 * k^2 - k) * (∑ i, ‖v i‖^2) ≤
        (∑ i, ∑ j, ((star (v i)) * A i j * v j).re) ∧
      (∑ i, ∑ j, ((star (v i)) * A i j * v j).re) ≤
        k * ∑ i, ‖v i‖^2 := by
  let B (i j : ι) : ℂ := if i = j then 0 else A i j
  have hB (i j : ι) : ‖B i j‖ = if i = j then 0 else ‖A i j‖ := by
    by_cases h : i = j <;> simp [B, h]
  have hs := weighted_schur (fun i j ↦ ‖B i j‖) (fun i ↦ ‖v i‖) (k - k^2)
    (fun _ _ ↦ norm_nonneg _) (fun i ↦ by simpa only [hB] using hrow i)
    (fun j ↦ by simpa only [hB] using hcol j)
  let off (i j : ι) := (star (v i) * B i j * v j).re
  have hoff (i j : ι) : |off i j| ≤ ‖B i j‖ * (‖v i‖ * ‖v j‖) := by
    refine (Complex.abs_re_le_norm _).trans_eq ?_
    simp only [norm_mul, norm_star]
    ring
  have hup : (∑ i, ∑ j, off i j) ≤ (k - k^2) * ∑ i, ‖v i‖^2 := by
    refine le_trans ?_ hs
    exact Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦
      (le_abs_self _).trans (hoff i j)
  have hdown : - (∑ i, ∑ j, off i j) ≤ (k - k^2) * ∑ i, ‖v i‖^2 := by
    simp only [← Finset.sum_neg_distrib]
    refine le_trans ?_ hs
    exact Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦
      (neg_le_abs _).trans (hoff i j)
  have hentry (i j : ι) :
      (star (v i) * A i j * v j).re =
        (if i = j then k^2 * ‖v i‖^2 else 0) + off i j := by
    by_cases h : i = j
    · subst j
      rw [hdiag i]
      rw [show star (v i) * (↑(k^2) : ℂ) * v i =
        (↑(k^2) : ℂ) * (star (v i) * v i) by ring]
      rw [show star (v i) * v i = (↑(‖v i‖^2) : ℂ) by
        simpa only [Complex.ofReal_pow, starRingEnd_apply] using Complex.conj_mul' (v i)]
      rw [← Complex.ofReal_mul, Complex.ofReal_re]
      simp [off, B]
    · simp [h, off, B]
  have htotal :
      (∑ i, ∑ j, (star (v i) * A i j * v j).re) =
        k^2 * (∑ i, ‖v i‖^2) + ∑ i, ∑ j, off i j := by
    simp only [hentry, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true,
      Finset.mul_sum]
  rw [htotal]
  constructor <;> nlinarith

/-- The same constants give a positive lower bound and a strict contraction. -/
theorem spectralWindowConstants (k : ℝ) (hk : 1 / 2 < k) (hk' : k < 1) :
    0 < 2 * k^2 - k ∧ 0 ≤ 1 + k - 2 * k^2 ∧ 1 + k - 2 * k^2 < 1 := by
  have hpos := mul_pos (show 0 < k by linarith) (show 0 < 2 * k - 1 by linarith)
  have hdef := mul_pos (show 0 < 1 - k by linarith) (show 0 < 1 + 2 * k by linarith)
  constructor
  · nlinarith
  · constructor <;> nlinarith

end Periodicity
