import Cat0Bounds.Geometry

namespace Cat0Bounds

variable {X : Type*} [MetricSpace X]

noncomputable def mann (G : Geometry X) (T : X → X) (l : ℝ) (x : X) : X :=
  G.mix l x (T x)

theorem mann_dist (G : Geometry X) (T : X → X) (l : ℝ) (hl0 : 0 ≤ l) (hl1 : l ≤ 1)
    (x : X) : dist x (mann G T l x) = l * dist x (T x) :=
  G.dist_left l x (T x) hl0 hl1

theorem mann_residual (G : Geometry X) {T : X → X} (hT : LipschitzWith 1 T)
    (l : ℝ) (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (x : X) :
    dist (mann G T l x) (T (mann G T l x)) ≤ dist x (T x) := by
  have ht := dist_triangle (mann G T l x) (T x) (T (mann G T l x))
  have hn := nonexpansive_dist hT x (mann G T l x)
  have hd := G.dist_right l x (T x) hl0 hl1
  have he := mann_dist G T l hl0 hl1 x
  change dist (mann G T l x) (T x) = _ at hd
  linarith only [ht, hn, hd, he]

theorem mix_two_points_sq (G : Geometry X) (l : ℝ) (hl0 : 0 ≤ l) (hl1 : l ≤ 1)
    (a b c e : X) :
    dist (G.mix l a b) (G.mix l c e) ^ 2 ≤
      (1 - l) * dist a c ^ 2 + l * dist b e ^ 2 := by
  have h1 := G.cn l a b (G.mix l c e) hl0 hl1
  have h2 := G.cn l c e a hl0 hl1
  have h3 := G.cn l c e b hl0 hl1
  rw [dist_comm (G.mix l c e) (G.mix l a b),
    dist_comm (G.mix l c e) a, dist_comm (G.mix l c e) b] at h1
  have h2m := mul_le_mul_of_nonneg_left h2 (sub_nonneg.mpr hl1)
  have h3m := mul_le_mul_of_nonneg_left h3 hl0
  have h4m := mul_le_mul_of_nonneg_left (G.four_point a b c e)
    (mul_nonneg hl0 (sub_nonneg.mpr hl1))
  have hsq := mul_nonneg (mul_nonneg hl0 (sub_nonneg.mpr hl1))
    (sq_nonneg (dist a b - dist c e))
  nlinarith only [h1, h2m, h3m, h4m, hsq]

theorem mann_nonexpansive (G : Geometry X) {T : X → X} (hT : LipschitzWith 1 T)
    (l : ℝ) (hl0 : 0 ≤ l) (hl1 : l ≤ 1) : LipschitzWith 1 (mann G T l) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul]
  have hq := mix_two_points_sq G l hl0 hl1 x (T x) y (T y)
  have hn := mul_le_mul_of_nonneg_left (nonexpansive_sq hT x y) hl0
  change dist (mann G T l x) (mann G T l y) ^ 2 ≤ _ at hq
  have hs : dist (mann G T l x) (mann G T l y) ^ 2 ≤ dist x y ^ 2 := by
    nlinarith only [hq, hn]
  nlinarith only [hs, dist_nonneg (x := x) (y := y)]

theorem mann_anchored_transfer (G : Geometry X) (T : X → X) (u z : X)
    (l c : ℝ) (hl0 : 0 < l) (hl1 : l ≤ 1)
    (h : c * dist z (mann G T l z) ^ 2 ≤
      dist u (mann G T l z) ^ 2 - dist u z ^ 2) :
    (1 - l + l * c) * dist z (T z) ^ 2 ≤ dist u (T z) ^ 2 - dist u z ^ 2 := by
  have hcn := G.cn l z (T z) u (le_of_lt hl0) hl1
  change dist u (mann G T l z) ^ 2 ≤ _ at hcn
  rw [mann_dist G T l (le_of_lt hl0) hl1, mul_pow] at h
  apply (mul_le_mul_iff_right₀ hl0).mp
  nlinarith only [h, hcn]

end Cat0Bounds
