import Cat0Bounds.Geometry
import Cat0Bounds.Scalar

/-! Comparison-point estimates without a fixed-point assumption.

Distance convexity is derived from the existing CN inequality and the
metric triangle inequality; it is not an additional geometric hypothesis.
-/

namespace Cat0Bounds

variable {X : Type*} [MetricSpace X]

/-- Convexity of distance along the chosen geodesics, derived from CN. -/
theorem convex_distance (G : Geometry X) (t : ℝ) (a b p : X)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    dist p (G.mix t a b) ≤ (1 - t) * dist p a + t * dist p b := by
  have ht : 0 ≤ 1 - t := sub_nonneg.mpr ht1
  have htri₁ : dist p a ≤ dist p b + dist a b := by
    simpa only [dist_comm b a] using dist_triangle p b a
  have htri₂ := dist_triangle p a b
  have hminus : 0 ≤ dist a b - (dist p a - dist p b) := by
    linarith only [htri₁]
  have hplus : 0 ≤ dist a b + (dist p a - dist p b) := by
    linarith only [htri₂]
  have hreverse : (dist p a - dist p b) ^ 2 ≤ dist a b ^ 2 := by
    nlinarith only [mul_nonneg hminus hplus]
  have hweighted := mul_le_mul_of_nonneg_left hreverse (mul_nonneg ht0 ht)
  have hcn := G.cn t a b p ht0 ht1
  have hsq : dist p (G.mix t a b) ^ 2 ≤
      ((1 - t) * dist p a + t * dist p b) ^ 2 := by
    nlinarith only [hcn, hweighted]
  have hmean : 0 ≤ (1 - t) * dist p a + t * dist p b := by positivity
  have hr : 0 ≤ dist p (G.mix t a b) := dist_nonneg
  nlinarith only [hsq, hmean, hr]

/-- The endpoint estimate with the displacement of an arbitrary point. -/
theorem endpoint_arbitrary (G : Geometry X) {T : X → X}
    (hT : LipschitzWith 1 T) (u z p : X) :
    dist u (T z) ^ 2 - dist u z ^ 2 ≤
      2 * dist u p * dist z (T z) + 2 * dist p (T p) * dist p z
        + dist p (T p) ^ 2 := by
  have hdist : dist p (T z) ≤ dist p (T p) + dist p z := by
    calc
      dist p (T z) ≤ dist p (T p) + dist (T p) (T z) := dist_triangle _ _ _
      _ ≤ dist p (T p) + dist p z := by
        have h := nonexpansive_dist hT p z
        linarith only [h]
  have hsq : dist p (T z) ^ 2 ≤ (dist p (T p) + dist p z) ^ 2 := by
    gcongr
  have hfour := G.four_point u p z (T z)
  nlinarith only [hfour, hsq]

/-- The factorization used to cancel the comparison-point displacement. -/
theorem comparison_factorization (r D δ κ : ℝ) :
    (r + δ) * (κ * r - κ * δ - 2 * D) =
      κ * r ^ 2 - κ * δ ^ 2 - 2 * D * (r + δ) := by
  ring

/-- Scalar endpoint cancellation, including the case of two zero residuals. -/
theorem comparison_residual_of_sq (r D δ κ : ℝ)
    (hr : 0 ≤ r) (hD : 0 ≤ D) (hδ : 0 ≤ δ) (hκ : 0 < κ)
    (h : κ * r ^ 2 ≤ 2 * D * (r + δ) + κ * δ ^ 2) :
    r ≤ δ + 2 * D / κ := by
  have hfactor : (r + δ) * (κ * r - κ * δ - 2 * D) ≤ 0 := by
    rw [comparison_factorization]
    linarith only [h]
  by_cases hzero : r + δ = 0
  · have hrzero : r = 0 := by linarith only [hr, hδ, hzero]
    rw [hrzero]
    positivity
  · have hpos : 0 < r + δ := lt_of_le_of_ne (add_nonneg hr hδ) (Ne.symm hzero)
    have hlinear : κ * r - κ * δ - 2 * D ≤ 0 := by
      by_contra hnot
      have hprod := mul_pos hpos (lt_of_not_ge hnot)
      linarith only [hfactor, hprod]
    have hdiv : r - δ ≤ 2 * D / κ := by
      apply (le_div_iff₀ hκ).2
      nlinarith only [hlinear]
    linarith only [hdiv]

/-- The comparison-point version of the endpoint lemma in version 3. -/
theorem endpoint_comparison (G : Geometry X) {T : X → X}
    (hT : LipschitzWith 1 T) (u z p : X) (κ : ℝ) (hκ : 0 < κ)
    (hphi : κ * dist z (T z) ^ 2 ≤ dist u (T z) ^ 2 - dist u z ^ 2)
    (hradius : dist p z ≤ dist u p + (κ - 1) / 2 * dist p (T p)) :
    dist z (T z) ≤ dist p (T p) + 2 * dist u p / κ := by
  have hend := endpoint_arbitrary G hT u z p
  have hδ : 0 ≤ 2 * dist p (T p) := by positivity
  have hradius' := mul_le_mul_of_nonneg_left hradius hδ
  apply comparison_residual_of_sq _ _ _ _ dist_nonneg dist_nonneg dist_nonneg hκ
  nlinarith only [hphi, hend, hradius']

end Cat0Bounds
