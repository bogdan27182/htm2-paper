import Cat0Bounds.Scalar

namespace Cat0Bounds

theorem family_two_cn_algebra (a n A B S Q D : ℝ) (ha : 1 ≤ a) (hn : a + 1 ≤ n)
    (h1 : D ≤ a / n * ((n - a - 1) / (n - 1)) ^ 2 * A
      + (n - a) / n * Q - a * (n - a) / n ^ 2 * B)
    (h2 : Q ≤ a / (n - 1) * B + (n - a - 1) / (n - 1) * S
      - a * (n - a - 1) / (n - 1) ^ 2 * A) :
    D ≤ -a * (n - a - 1) / (n * (n - 1) ^ 2) * A
      + a * (n - a) / (n ^ 2 * (n - 1)) * B
      + (n - a) * (n - a - 1) / (n * (n - 1)) * S := by
  have hn0 : 0 < n := by linarith
  have hn1 : 0 < n - 1 := by linarith
  have hna : 0 ≤ n - a := by linarith
  calc
    D ≤ a / n * ((n - a - 1) / (n - 1)) ^ 2 * A
      + (n - a) / n * (a / (n - 1) * B + (n - a - 1) / (n - 1) * S
        - a * (n - a - 1) / (n - 1) ^ 2 * A)
      - a * (n - a) / n ^ 2 * B := by
        have hm := mul_le_mul_of_nonneg_left h2 (show 0 ≤ (n - a) / n by positivity)
        linarith only [h1, hm]
    _ = _ := by field_simp; ring

theorem family_increment_algebra (a n x y c r : ℝ) (ha : 1 ≤ a) (hn : a + 1 ≤ n)
    (_hx : 0 ≤ x) (hy : 0 ≤ y) (hc : 0 ≤ c)
    (hrec : r ^ 2 ≤ -a * (n - a - 1) / (n * (n - 1) ^ 2) * x ^ 2
      + a * (n - a) / (n ^ 2 * (n - 1)) * y ^ 2
      + (n - a) * (n - a - 1) / (n * (n - 1)) * c ^ 2)
    (hprev : c ≤ x / (n - 1)) (htri : y ≤ x + c) : r ≤ y / n := by
  have hn0 : 0 < n := by linarith
  have hn1 : 0 < n - 1 := by linarith
  have hna : 0 ≤ n - a := by linarith
  have hna1 : 0 ≤ n - a - 1 := by linarith
  have ha1 : 0 ≤ a - 1 := by linarith
  have hc2 : c ^ 2 ≤ x ^ 2 / (n - 1) ^ 2 := by
    rw [← div_pow]
    gcongr
  have hrec2 : r ^ 2 ≤ a * (n - a) / (n ^ 2 * (n - 1)) * y ^ 2
      - (a - 1) * (n - a - 1) / (n - 1) ^ 3 * x ^ 2 := by
    calc
      _ ≤ -a * (n - a - 1) / (n * (n - 1) ^ 2) * x ^ 2
        + a * (n - a) / (n ^ 2 * (n - 1)) * y ^ 2
        + (n - a) * (n - a - 1) / (n * (n - 1)) * c ^ 2 := hrec
      _ ≤ -a * (n - a - 1) / (n * (n - 1) ^ 2) * x ^ 2
        + a * (n - a) / (n ^ 2 * (n - 1)) * y ^ 2
        + (n - a) * (n - a - 1) / (n * (n - 1)) * (x ^ 2 / (n - 1) ^ 2) := by
          gcongr
      _ = _ := by field_simp; ring
  have htri2 : y ≤ n / (n - 1) * x := by
    calc
      y ≤ x + x / (n - 1) := by linarith only [htri, hprev]
      _ = _ := by field_simp; ring
  have hy2 : y ^ 2 ≤ (n / (n - 1) * x) ^ 2 := by gcongr
  have hxy : (n - 1) ^ 2 / n ^ 2 * y ^ 2 ≤ x ^ 2 := by
    calc
      _ ≤ (n - 1) ^ 2 / n ^ 2 * (n / (n - 1) * x) ^ 2 :=
        mul_le_mul_of_nonneg_left hy2 (by positivity)
      _ = _ := by field_simp
  have hfinal : r ^ 2 ≤ y ^ 2 / n ^ 2 := by
    calc
      _ ≤ a * (n - a) / (n ^ 2 * (n - 1)) * y ^ 2
        - (a - 1) * (n - a - 1) / (n - 1) ^ 3 * x ^ 2 := hrec2
      _ ≤ a * (n - a) / (n ^ 2 * (n - 1)) * y ^ 2
        - (a - 1) * (n - a - 1) / (n - 1) ^ 3 *
          ((n - 1) ^ 2 / n ^ 2 * y ^ 2) := by
          have hm := mul_le_mul_of_nonneg_left hxy
            (show 0 ≤ (a - 1) * (n - a - 1) / (n - 1) ^ 3 by positivity)
          linarith only [hm]
      _ = _ := by field_simp; ring
  rw [← div_pow] at hfinal
  have hyd : 0 ≤ y / n := by positivity
  nlinarith only [hfinal, hyd]

theorem family_anchored_algebra (a n x y c r : ℝ) (ha : 1 ≤ a) (hn : a ≤ n)
    (hrs : c ^ 2 + (a - 1) / (a + 1) * r ^ 2 ≤ a ^ 2 / n ^ 2 * x ^ 2)
    (hcn : r ^ 2 ≤ a / n * y ^ 2 + (n - a) / n * c ^ 2
      - a * (n - a) / n ^ 2 * x ^ 2) :
    (2 * n - a + 1) / (a + 1) * r ^ 2 ≤
      y ^ 2 - ((n - a) / n) ^ 2 * x ^ 2 := by
  have ha0 : 0 < a := by linarith
  have hap : 0 < a + 1 := by linarith
  have hn0 : 0 < n := by linarith
  have hna : 0 ≤ n - a := by linarith
  have hdefCN := mul_nonneg (show 0 ≤ n / a by positivity) (sub_nonneg.mpr hcn)
  have hdefRS := mul_nonneg (show 0 ≤ (n - a) / a by positivity) (sub_nonneg.mpr hrs)
  have hid : y ^ 2 - ((n - a) / n) ^ 2 * x ^ 2
      - (2 * n - a + 1) / (a + 1) * r ^ 2 =
      n / a * (a / n * y ^ 2 + (n - a) / n * c ^ 2
        - a * (n - a) / n ^ 2 * x ^ 2 - r ^ 2)
      + (n - a) / a * (a ^ 2 / n ^ 2 * x ^ 2
        - (c ^ 2 + (a - 1) / (a + 1) * r ^ 2)) := by
    field_simp
    ring
  linarith only [hdefCN, hdefRS, hid]

end Cat0Bounds
