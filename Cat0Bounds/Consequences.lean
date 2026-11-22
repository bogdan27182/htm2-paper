import Cat0Bounds.Family
import Cat0Bounds.Adaptive
import Cat0Bounds.Displacement
import Cat0Bounds.Stronger

/-! Minimal-displacement convergence and strengthened bounds for the v3
iterations. These use the same explicit geometric hypotheses as the main
comparison theorems, without completeness or boundedness assumptions.
-/

namespace Cat0Bounds

open Filter

variable {X : Type*} [MetricSpace X]

theorem family_displacement_tendsto (G : Geometry X) {T : X → X}
    (hT : LipschitzWith 1 T) (u : X) (a l : ℝ)
    (ha : 1 ≤ a) (hl0 : 0 < l) (hl1 : l ≤ 1) :
    Tendsto (fun n => dist (family G T u a l n) (T (family G T u a l n)))
      atTop (nhds (minimalDisplacement T)) := by
  apply residual_tendsto_of_reciprocal_comparison T u (family G T u a l)
    1 (2 * l / (a + 1)) (by norm_num) (by positivity)
  intro p n
  convert family_bound G hT u p a l ha hl0 hl1 n using 1
  simp only [familyKappa]
  congr 2
  ring

theorem family_endpoint_displacement_tendsto (G : Geometry X) {T : X → X}
    (hT : LipschitzWith 1 T) (u : X) (a l : ℝ)
    (ha : 1 ≤ a) (hl0 : 0 < l) (hl1 : l ≤ 1) :
    Tendsto (fun n => dist (familyIter G T u a l n) (T (familyIter G T u a l n)))
      atTop (nhds (minimalDisplacement T)) := by
  apply residual_tendsto_of_reciprocal_comparison T u (familyIter G T u a l)
    1 (2 * l / (a + 1)) (by norm_num) (by positivity)
  intro p n
  convert family_endpoint_bound G hT u p a l ha hl0 hl1 n using 1
  simp only [familyKappa]
  congr 2
  ring

theorem adaptive_displacement_tendsto (G : Geometry X) {T : X → X}
    (hT : LipschitzWith 1 T) (u : X) :
    Tendsto (fun n => dist (adaptive G T u n) (T (adaptive G T u n)))
      atTop (nhds (minimalDisplacement T)) := by
  apply residual_tendsto_of_reciprocal_comparison T u (adaptive G T u)
    1 1 (by norm_num) (by norm_num)
  intro p n
  simpa [add_comm] using adaptive_horizon_bound G hT u p n

theorem family_displacement_rate (G : Geometry X) {T : X → X}
    (hT : LipschitzWith 1 T) (u p : X) (a l : ℝ)
    (ha : 1 ≤ a) (hl0 : 0 < l) (hl1 : l ≤ 1)
    (hp : dist p (T p) = minimalDisplacement T) (n : ℕ) :
    0 ≤ dist (family G T u a l n) (T (family G T u a l n)) - minimalDisplacement T ∧
      dist (family G T u a l n) (T (family G T u a l n)) - minimalDisplacement T
        ≤ 2 * dist u p / familyKappa a l n := by
  have hlow := minimalDisplacement_le T (family G T u a l n)
  have hupp := family_bound G hT u p a l ha hl0 hl1 n
  rw [hp] at hupp
  constructor <;> linarith

theorem adaptive_displacement_rate (G : Geometry X) {T : X → X}
    (hT : LipschitzWith 1 T) (u p : X)
    (hp : dist p (T p) = minimalDisplacement T) (n : ℕ) :
    0 ≤ dist (adaptive G T u n) (T (adaptive G T u n)) - minimalDisplacement T ∧
      dist (adaptive G T u n) (T (adaptive G T u n)) - minimalDisplacement T
        ≤ 2 * dist u p / ((n : ℝ) + 1) := by
  have hlow := minimalDisplacement_le T (adaptive G T u n)
  have hupp := adaptive_horizon_bound G hT u p n
  rw [hp] at hupp
  constructor <;> linarith

theorem family_endpoint_displacement_rate (G : Geometry X) {T : X → X}
    (hT : LipschitzWith 1 T) (u p : X) (a l : ℝ)
    (ha : 1 ≤ a) (hl0 : 0 < l) (hl1 : l ≤ 1)
    (hp : dist p (T p) = minimalDisplacement T) (n : ℕ) :
    0 ≤ dist (familyIter G T u a l n) (T (familyIter G T u a l n)) - minimalDisplacement T ∧
      dist (familyIter G T u a l n) (T (familyIter G T u a l n)) - minimalDisplacement T
        ≤ 2 * dist u p / familyKappa a l n := by
  have hlow := minimalDisplacement_le T (familyIter G T u a l n)
  have hupp := family_endpoint_bound G hT u p a l ha hl0 hl1 n
  rw [hp] at hupp
  constructor <;> linarith

theorem family_stronger_bound (G : Geometry X) {T : X → X}
    (hT : LipschitzWith 1 T) (u p : X) (a l σ : ℝ)
    (ha : 1 ≤ a) (hl0 : 0 < l) (hl1 : l ≤ 1) (hσ : 0 ≤ σ)
    (hstrong : ∀ z, dist p (T z) ^ 2 ≤ dist p z ^ 2 - σ * dist z (T z) ^ 2)
    (n : ℕ) :
    dist (family G T u a l n) (T (family G T u a l n))
      ≤ 2 * dist u p / (familyKappa a l n + σ) := by
  apply residual_stronger G T u p _ _ σ
  · have := familyKappa_pos a l ha (le_of_lt hl0) n
    linarith
  · exact family_anchored G hT u a l ha hl0 hl1 n
  · exact hstrong _

theorem family_endpoint_stronger_bound (G : Geometry X) {T : X → X}
    (hT : LipschitzWith 1 T) (u p : X) (a l σ : ℝ)
    (ha : 1 ≤ a) (hl0 : 0 < l) (hl1 : l ≤ 1) (hσ : 0 ≤ σ)
    (hstrong : ∀ z, dist p (T z) ^ 2 ≤ dist p z ^ 2 - σ * dist z (T z) ^ 2)
    (n : ℕ) :
    dist (familyIter G T u a l n) (T (familyIter G T u a l n))
      ≤ 2 * dist u p / (familyKappa a l n + σ) := by
  rw [familyIter_eq_mann]
  exact le_trans (mann_residual G hT l (le_of_lt hl0) hl1 _)
    (family_stronger_bound G hT u p a l σ ha hl0 hl1 hσ hstrong n)

theorem adaptive_stronger_bound (G : Geometry X) {T : X → X}
    (hT : LipschitzWith 1 T) (u p : X) (σ : ℝ) (hσ : 0 ≤ σ)
    (hstrong : ∀ z, dist p (T z) ^ 2 ≤ dist p z ^ 2 - σ * dist z (T z) ^ 2)
    (n : ℕ) (hn : T (adaptive G T u n) ≠ adaptive G T u n) :
    dist (adaptive G T u n) (T (adaptive G T u n))
      ≤ 2 * dist u p / (adaptiveCoeff T u (adaptive G T u n) + σ) := by
  apply residual_stronger G T u p _ _ σ
  · have hlow := adaptiveCoeff_lower G hT u n hn
    have hnat : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  · exact le_of_eq (adaptiveCoeff_mul T u (adaptive G T u n) hn)
  · exact hstrong _

end Cat0Bounds
