import Cat0Bounds.Geometry
import Cat0Bounds.Scalar

/-! The endpoint estimate under the stronger fixed-point inequality in v3.

The one-point hypothesis below is exactly the inequality used at the
terminal iterate. Nonexpansiveness enters the iteration's anchored
estimate, rather than this final algebraic step.
-/

namespace Cat0Bounds

variable {X : Type*} [MetricSpace X]

theorem endpoint_stronger (G : Geometry X) (T : X → X)
    (u p z : X) (σ : ℝ)
    (hstrong : dist p (T z) ^ 2 ≤ dist p z ^ 2 - σ * dist z (T z) ^ 2) :
    dist u (T z) ^ 2 - dist u z ^ 2 + σ * dist z (T z) ^ 2
      ≤ 2 * dist u p * dist z (T z) := by
  have hfour := G.four_point u p z (T z)
  linarith

theorem residual_stronger (G : Geometry X) (T : X → X)
    (u p z : X) (κ σ : ℝ) (hκσ : 0 < κ + σ)
    (hanchor : κ * dist z (T z) ^ 2 ≤ dist u (T z) ^ 2 - dist u z ^ 2)
    (hstrong : dist p (T z) ^ 2 ≤ dist p z ^ 2 - σ * dist z (T z) ^ 2) :
    dist z (T z) ≤ 2 * dist u p / (κ + σ) := by
  apply residual_of_sq _ _ _ dist_nonneg dist_nonneg hκσ
  have h := endpoint_stronger G T u p z σ hstrong
  nlinarith only [h, hanchor]

end Cat0Bounds
