import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The factorial induction in the one-sided uniqueness proofs

Both proofs obtain a recurrence for the derivative moments. This file
proves the factorial bound from that recurrence and the exponential
smallness condition.
-/

namespace Periodicity

open scoped BigOperators

private theorem normalizedTerm {r p : ℕ} (hp : p ≤ r)
    (b H M : ℝ) (hH : 0 < H) :
    (r.choose p : ℝ) * b^p * (M * H^(r-p) * ((r-p).factorial : ℝ)) =
      (M * H^r * (r.factorial : ℝ)) * ((b/H)^p / (p.factorial : ℝ)) := by
  have hf : (r.choose p : ℝ) * (p.factorial : ℝ) * ((r-p).factorial : ℝ) =
      (r.factorial : ℝ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hp
  have hh : H^p * H^(r-p) = H^r := by
    rw [← pow_add, Nat.add_sub_of_le hp]
  rw [div_pow, div_div, ← mul_div_assoc]
  apply (eq_div_iff (by positivity : H^p * (p.factorial : ℝ) ≠ 0)).2
  calc
    _ = (M * (H^p * H^(r-p)) *
          ((r.choose p : ℝ) * (p.factorial : ℝ) * ((r-p).factorial : ℝ))) * b^p := by
      ring
    _ = _ := by rw [hh, hf]

/-- The factorial bound for the derivative moments used by both papers.
The sum uses p+1 to index the positive terms in the recurrence. -/
theorem factorialMomentBound (D : ℕ → ℝ) (C₁ C₂ R b H M : ℝ)
    (hC₂ : 0 ≤ C₂) (hR : 0 ≤ R) (hb : 0 ≤ b) (hH : 0 < H)
    (hRH : R ≤ H) (hM : 0 ≤ M)
    (hsmall : C₂ * (Real.exp (b/H) - 1) ≤ 1/2)
    (hbase : D 0 ≤ M) (hMlarge : 2 * C₁ ≤ M)
    (hrec : ∀ r : ℕ, D r ≤ C₁ * R^r * (r.factorial : ℝ) +
      C₂ * ∑ p ∈ Finset.range r,
        (r.choose (p+1) : ℝ) * b^(p+1) * D (r-(p+1))) :
    ∀ r : ℕ, D r ≤ M * H^r * (r.factorial : ℝ) := by
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
    by_cases hr : r = 0
    · simpa [hr] using hbase
    have hfirst : C₁ * R^r * (r.factorial : ℝ) ≤
        (M / 2) * H^r * (r.factorial : ℝ) := by
      gcongr
      linarith
    let a (p : ℕ) := (b/H)^p / (p.factorial : ℝ)
    have hseries : (∑ p ∈ Finset.range r, a (p+1)) ≤ Real.exp (b/H) - 1 := by
      have h := Real.sum_le_exp_of_nonneg (div_nonneg hb hH.le) (r+1)
      change (∑ p ∈ Finset.range (r+1), a p) ≤ _ at h
      rw [Finset.sum_range_succ'] at h
      have ha : a 0 = 1 := by simp [a]
      rw [ha] at h
      linarith
    have hsum :
        (∑ p ∈ Finset.range r, (r.choose (p+1) : ℝ) * b^(p+1) * D (r-(p+1))) ≤
          (M * H^r * (r.factorial : ℝ)) * ∑ p ∈ Finset.range r, a (p+1) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro p hp
      have hpr := Finset.mem_range.mp hp
      refine (mul_le_mul_of_nonneg_left (ih _ (by omega)) (by positivity)).trans_eq ?_
      exact normalizedTerm (by omega) b H M hH
    have hsecond :
        C₂ * (∑ p ∈ Finset.range r, (r.choose (p+1) : ℝ) * b^(p+1) * D (r-(p+1))) ≤
          (M / 2) * H^r * (r.factorial : ℝ) := by
      calc
        _ ≤ C₂ * ((M * H^r * (r.factorial : ℝ)) * ∑ p ∈ Finset.range r, a (p+1)) :=
          mul_le_mul_of_nonneg_left hsum hC₂
        _ = (M * H^r * (r.factorial : ℝ)) * (C₂ * ∑ p ∈ Finset.range r, a (p+1)) := by
          ring
        _ ≤ (M * H^r * (r.factorial : ℝ)) * (1/2) :=
          mul_le_mul_of_nonneg_left
            ((mul_le_mul_of_nonneg_left hseries hC₂).trans hsmall) (by positivity)
        _ = _ := by ring
    calc
      D r ≤ _ := hrec r
      _ ≤ _ := add_le_add hfirst hsecond
      _ = _ := by ring

end Periodicity
