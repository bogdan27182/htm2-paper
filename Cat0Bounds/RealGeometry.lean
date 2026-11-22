import Cat0Bounds.Geometry

namespace Cat0Bounds

/-- The explicit geometric hypotheses hold for the ordinary real line. -/
noncomputable def realGeometry : Geometry ℝ where
  mix t a b := (1 - t) * a + t * b
  dist_left t a b ht _ := by
    simp only [Real.dist_eq]
    rw [show a - ((1 - t) * a + t * b) = t * (a - b) by ring]
    rw [abs_mul, abs_of_nonneg ht]
  dist_right t a b _ ht := by
    simp only [Real.dist_eq]
    rw [show (1 - t) * a + t * b - b = (1 - t) * (a - b) by ring]
    rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1 - t)]
  cn t a b z _ _ := by
    simp only [Real.dist_eq, sq_abs]
    apply le_of_eq
    ring
  four_point a b c e := by
    simp only [Real.dist_eq, sq_abs]
    have h : (a - b) * (c - e) ≤ |a - b| * |c - e| := by
      rw [← abs_mul]
      exact le_abs_self _
    nlinarith only [h]

/-- The common extremal mapping from Section 5. -/
noncomputable def extremizer (q t : ℝ) : ℝ := q / 2 - |t + q / 2|

theorem extremizer_left (q t : ℝ) (ht : t ≤ -q / 2) : extremizer q t = t + q := by
  unfold extremizer
  rw [abs_of_nonpos (by linarith : t + q / 2 ≤ 0)]
  ring

theorem extremizer_right (q t : ℝ) (ht : -q / 2 ≤ t) : extremizer q t = -t := by
  unfold extremizer
  rw [abs_of_nonneg (by linarith : 0 ≤ t + q / 2)]
  ring

theorem extremizer_fixed (q : ℝ) (hq : 0 ≤ q) : extremizer q 0 = 0 := by
  rw [extremizer_right q 0 (by linarith)]
  ring

theorem extremizer_nonexpansive (q : ℝ) : LipschitzWith 1 (extremizer q) := by
  apply LipschitzWith.mk_one
  intro x y
  have h := dist_triangle (x + q / 2) (y + q / 2) (0 : ℝ)
  have h' := dist_triangle (y + q / 2) (x + q / 2) (0 : ℝ)
  simp only [Real.dist_eq, sub_zero] at h h'
  have he : x + q / 2 - (y + q / 2) = x - y := by ring
  have he' : y + q / 2 - (x + q / 2) = -(x - y) := by ring
  rw [he] at h
  rw [he', abs_neg] at h'
  simp only [extremizer, Real.dist_eq]
  apply abs_le.mpr
  constructor <;> linarith only [h, h']

end Cat0Bounds
