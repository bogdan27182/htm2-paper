import Cat0Bounds.Family
import Cat0Bounds.Adaptive

/-! The displacement coefficient is separately optimal.

The unit translation has residual one everywhere. Taking the comparison
point equal to the anchor makes the distance term zero at every horizon.
This proves separate coefficient optimality, not simultaneous sharpness
for prescribed positive distance and displacement.
-/

namespace Cat0Bounds

def unitTranslation (t : ℝ) : ℝ := t + 1

theorem unitTranslation_nonexpansive : LipschitzWith 1 unitTranslation := by
  apply LipschitzWith.mk_one
  intro x y
  simp only [unitTranslation, Real.dist_eq]
  rw [show x + 1 - (y + 1) = x - y by ring]

theorem unitTranslation_residual (t : ℝ) : dist t (unitTranslation t) = 1 := by
  rw [unitTranslation, Real.dist_eq, show t - (t + 1) = -1 by ring]
  norm_num

theorem unitTranslation_nonfixed (t : ℝ) : unitTranslation t ≠ t := by
  unfold unitTranslation
  linarith

/-- The same explicit instance has zero anchor distance and residual one
for both iterations at every horizon. -/
theorem comparison_translation_instance (a l : ℝ) (N : ℕ) :
    LipschitzWith 1 unitTranslation ∧ dist (0 : ℝ) 0 = 0 ∧
      dist (0 : ℝ) (unitTranslation 0) = 1 ∧
      dist (family realGeometry unitTranslation 0 a l N)
        (unitTranslation (family realGeometry unitTranslation 0 a l N)) = 1 ∧
      dist (adaptive realGeometry unitTranslation 0 N)
        (unitTranslation (adaptive realGeometry unitTranslation 0 N)) = 1 := by
  exact ⟨unitTranslation_nonexpansive, dist_self _, unitTranslation_residual _,
    unitTranslation_residual _, unitTranslation_residual _⟩

/-- Any uniform family comparison bound of the stated form must put
coefficient at least one on the comparison-point displacement. -/
theorem family_displacement_coefficient_optimal (a l C : ℝ) (N : ℕ)
    (hbound : ∀ (T : ℝ → ℝ), LipschitzWith 1 T → ∀ (u p : ℝ),
      dist (family realGeometry T u a l N) (T (family realGeometry T u a l N)) ≤
        C * dist p (T p) + 2 * dist u p / familyKappa a l N) :
    1 ≤ C := by
  have h := hbound unitTranslation unitTranslation_nonexpansive 0 0
  simpa only [unitTranslation_residual, dist_self, mul_zero, zero_div,
    mul_one, add_zero] using h

/-- The same necessary coefficient holds for the adaptive comparison
bound, with its explicitly nonfixed-iterate qualification. -/
theorem adaptive_displacement_coefficient_optimal (C : ℝ) (N : ℕ)
    (hbound : ∀ (T : ℝ → ℝ), LipschitzWith 1 T → ∀ (u p : ℝ),
      T (adaptive realGeometry T u N) ≠ adaptive realGeometry T u N →
      dist (adaptive realGeometry T u N) (T (adaptive realGeometry T u N)) ≤
        C * dist p (T p) +
          2 * dist u p / adaptiveCoeff T u (adaptive realGeometry T u N)) :
    1 ≤ C := by
  have h := hbound unitTranslation unitTranslation_nonexpansive 0 0
    (unitTranslation_nonfixed _)
  simpa only [unitTranslation_residual, dist_self, mul_zero, zero_div,
    mul_one, add_zero] using h

end Cat0Bounds
