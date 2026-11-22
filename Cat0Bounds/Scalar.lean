import Mathlib

namespace Cat0Bounds

/-- Cancellation in the last step of Lemma 2.1, including zero residual. -/
theorem residual_of_sq (r D κ : ℝ)
    (hr : 0 ≤ r) (hD : 0 ≤ D) (hκ : 0 < κ)
    (h : κ * r ^ 2 ≤ 2 * D * r) : r ≤ 2 * D / κ := by
  apply (le_div_iff₀ hκ).2
  by_cases hr0 : r = 0
  · simp only [hr0, zero_mul]
    positivity
  · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
    by_contra hnot
    have hg : 0 < r * κ - 2 * D := sub_pos.mpr (lt_of_not_ge hnot)
    have hp : 0 < (r * κ - 2 * D) * r := mul_pos hg hrpos
    nlinarith [h]

/-- Rational coefficient cancellation in the Halpern potential. The
variables `r`, `r'`, `a`, `b`, `b'` stand for squared distances. -/
theorem halpern_algebra (k r r' a b b' : ℝ) (hk : 0 ≤ k)
    (h : r' ≤ (1 / (k + 2)) * b'
      + (1 / (k + 2)) * ((k + 1) / (k + 2)) * a
      + ((k + 1) / (k + 2)) ^ 2 * r
      - (1 / (k + 2)) * ((k + 1) / (k + 2))
        * (1 + (k + 1) / (k + 2)) * b) :
    (k + 2) ^ 2 * r'
        + (k + 2) * (((k + 1) / (k + 2)) ^ 2 * b - b')
      ≤ (k + 1) ^ 2 * r + (k + 1) * (a - b) := by
  have hk2 : k + 2 ≠ 0 := ne_of_gt (by linarith)
  calc
    _ ≤ (k + 2) ^ 2 * ((1 / (k + 2)) * b'
        + (1 / (k + 2)) * ((k + 1) / (k + 2)) * a
        + ((k + 1) / (k + 2)) ^ 2 * r
        - (1 / (k + 2)) * ((k + 1) / (k + 2))
          * (1 + (k + 1) / (k + 2)) * b)
        + (k + 2) * (((k + 1) / (k + 2)) ^ 2 * b - b') := by
      have hm := mul_le_mul_of_nonneg_left h (sq_nonneg (k + 2))
      linarith only [hm]
    _ = _ := by field_simp; ring

end Cat0Bounds
