import Cat0Bounds.Scalar

namespace Cat0Bounds

/-- Combining the two CN inequalities in the increment proof. -/
theorem tm_two_cn_algebra (n A B S Q D : ℝ) (hn : 3 ≤ n)
    (h1 : D ≤ 2 / n * ((n - 3) / (n - 1)) ^ 2 * A
      + (n - 2) / n * Q - 2 * (n - 2) / n ^ 2 * B)
    (h2 : Q ≤ 2 / (n - 1) * B + (n - 3) / (n - 1) * S
      - 2 * (n - 3) / (n - 1) ^ 2 * A) :
    D ≤ -2 * (n - 3) / (n * (n - 1) ^ 2) * A
      + 2 * (n - 2) / (n ^ 2 * (n - 1)) * B
      + (n - 2) * (n - 3) / (n * (n - 1)) * S := by
  have hn0 : 0 < n := by linarith
  have hn1 : 0 < n - 1 := by linarith
  have hn2 : 0 ≤ n - 2 := by linarith
  have hc : 0 ≤ (n - 2) / n := by positivity
  calc
    D ≤ 2 / n * ((n - 3) / (n - 1)) ^ 2 * A
      + (n - 2) / n * (2 / (n - 1) * B + (n - 3) / (n - 1) * S
        - 2 * (n - 3) / (n - 1) ^ 2 * A)
      - 2 * (n - 2) / n ^ 2 * B := by
        have hm := mul_le_mul_of_nonneg_left h2 hc
        linarith only [h1, hm]
    _ = _ := by field_simp; ring

/-- The scalar induction in Lemma 4.1, written with distances rather
than square roots of squared distances. -/
theorem tm_increment_algebra (n a b c r : ℝ) (hn : 4 ≤ n)
    (_ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (_hr : 0 ≤ r)
    (hrec : r ^ 2 ≤ -2 * (n - 3) / (n * (n - 1) ^ 2) * a ^ 2
      + 2 * (n - 2) / (n ^ 2 * (n - 1)) * b ^ 2
      + (n - 2) * (n - 3) / (n * (n - 1)) * c ^ 2)
    (hprev : c ≤ a / (n - 1)) (htri : b ≤ a + c) : r ≤ b / n := by
  have hn0 : 0 < n := by linarith
  have hn1 : 0 < n - 1 := by linarith
  have hn2 : 0 < n - 2 := by linarith
  have hn3 : 0 < n - 3 := by linarith
  have hc2 : c ^ 2 ≤ a ^ 2 / (n - 1) ^ 2 := by
    rw [← div_pow]
    gcongr
  have hrec2 : r ^ 2 ≤ 2 * (n - 2) / (n ^ 2 * (n - 1)) * b ^ 2
      - (n - 3) / (n - 1) ^ 3 * a ^ 2 := by
    calc
      _ ≤ -2 * (n - 3) / (n * (n - 1) ^ 2) * a ^ 2
        + 2 * (n - 2) / (n ^ 2 * (n - 1)) * b ^ 2
        + (n - 2) * (n - 3) / (n * (n - 1)) * c ^ 2 := hrec
      _ ≤ -2 * (n - 3) / (n * (n - 1) ^ 2) * a ^ 2
        + 2 * (n - 2) / (n ^ 2 * (n - 1)) * b ^ 2
        + (n - 2) * (n - 3) / (n * (n - 1)) * (a ^ 2 / (n - 1) ^ 2) := by
          gcongr
      _ = _ := by field_simp; ring
  have htri2 : b ≤ n / (n - 1) * a := by
    calc
      b ≤ a + a / (n - 1) := by linarith only [htri, hprev]
      _ = _ := by field_simp; ring
  have hb2 : b ^ 2 ≤ (n / (n - 1) * a) ^ 2 := by gcongr
  have hab : (n - 1) ^ 2 / n ^ 2 * b ^ 2 ≤ a ^ 2 := by
    calc
      _ ≤ (n - 1) ^ 2 / n ^ 2 * (n / (n - 1) * a) ^ 2 := by
        exact mul_le_mul_of_nonneg_left hb2 (by positivity)
      _ = _ := by field_simp
  have hfinal : r ^ 2 ≤ b ^ 2 / n ^ 2 := by
    calc
      _ ≤ 2 * (n - 2) / (n ^ 2 * (n - 1)) * b ^ 2
        - (n - 3) / (n - 1) ^ 3 * a ^ 2 := hrec2
      _ ≤ 2 * (n - 2) / (n ^ 2 * (n - 1)) * b ^ 2
        - (n - 3) / (n - 1) ^ 3 * ((n - 1) ^ 2 / n ^ 2 * b ^ 2) := by
          have hm := mul_le_mul_of_nonneg_left hab
            (show 0 ≤ (n - 3) / (n - 1) ^ 3 by positivity)
          linarith only [hm]
      _ = _ := by field_simp; ring
  rw [← div_pow] at hfinal
  have hbdiv : 0 ≤ b / n := by positivity
  nlinarith only [hfinal, hbdiv]

/-- The final rearrangement in Lemma 4.2. -/
theorem tm_anchored_algebra (n a b c r : ℝ) (hn : 3 ≤ n)
    (hrs : r ^ 2 + 3 * c ^ 2 ≤ 12 / n ^ 2 * a ^ 2)
    (hcn : r ^ 2 ≤ 2 / n * b ^ 2 + (n - 2) / n * c ^ 2
      - 2 * (n - 2) / n ^ 2 * a ^ 2) :
    (2 * n - 1) / 3 * r ^ 2 ≤ b ^ 2 - ((n - 2) / n) ^ 2 * a ^ 2 := by
  have hn0 : 0 < n := by linarith
  have hn2 : 0 ≤ n - 2 := by linarith
  have hdefCN : 0 ≤ n / 2 *
      (2 / n * b ^ 2 + (n - 2) / n * c ^ 2
        - 2 * (n - 2) / n ^ 2 * a ^ 2 - r ^ 2) :=
    mul_nonneg (by positivity) (sub_nonneg.mpr hcn)
  have hdefRS : 0 ≤ (n - 2) / 6 *
      (12 / n ^ 2 * a ^ 2 - r ^ 2 - 3 * c ^ 2) := by
    apply mul_nonneg (by positivity)
    linarith only [hrs]
  have hid : b ^ 2 - ((n - 2) / n) ^ 2 * a ^ 2 - (2 * n - 1) / 3 * r ^ 2 =
      n / 2 * (2 / n * b ^ 2 + (n - 2) / n * c ^ 2
        - 2 * (n - 2) / n ^ 2 * a ^ 2 - r ^ 2)
      + (n - 2) / 6 * (12 / n ^ 2 * a ^ 2 - r ^ 2 - 3 * c ^ 2) := by
    field_simp
    ring
  linarith only [hdefCN, hdefRS, hid]

end Cat0Bounds
