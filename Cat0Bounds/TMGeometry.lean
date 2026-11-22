import Cat0Bounds.Geometry
import Cat0Bounds.TMScalar

namespace Cat0Bounds

variable {X : Type*} [MetricSpace X]

/-- The two geometric comparisons behind Lemma 4.1. -/
theorem tm_two_cn (G : Geometry X) (u a b : X) (n : ℝ) (hn : 4 ≤ n) :
    dist (G.mix ((n - 3) / (n - 1)) u a) (G.mix ((n - 2) / n) u b) ^ 2 ≤
      -2 * (n - 3) / (n * (n - 1) ^ 2) * dist u a ^ 2
        + 2 * (n - 2) / (n ^ 2 * (n - 1)) * dist u b ^ 2
        + (n - 2) * (n - 3) / (n * (n - 1)) * dist a b ^ 2 := by
  have hn0 : 0 < n := by linarith
  have hn1 : 0 < n - 1 := by linarith
  have hn2 : 0 ≤ n - 2 := by linarith
  have hn3 : 0 ≤ n - 3 := by linarith
  let s := (n - 2) / n
  let sp := (n - 3) / (n - 1)
  let v := G.mix sp u a
  let w := G.mix s u b
  have hs0 : 0 ≤ s := by dsimp [s]; positivity
  have hsp0 : 0 ≤ sp := by dsimp [sp]; positivity
  have hs1 : s ≤ 1 := by dsimp [s]; apply (div_le_iff₀ hn0).2; linarith
  have hsp1 : sp ≤ 1 := by dsimp [sp]; apply (div_le_iff₀ hn1).2; linarith
  have hs : 1 - s = 2 / n := by dsimp [s]; field_simp; ring
  have hsp : 1 - sp = 2 / (n - 1) := by dsimp [sp]; field_simp; ring
  have hd : dist u v = sp * dist u a := G.dist_left sp u a hsp0 hsp1
  have h1 := G.cn s u b v hs0 hs1
  have h2 := G.cn sp u a b hsp0 hsp1
  change dist v w ^ 2 ≤ _ at h1
  change dist b v ^ 2 ≤ _ at h2
  rw [dist_comm v u, hd, mul_pow, hs] at h1
  rw [dist_comm b v, dist_comm b u, dist_comm b a, hsp] at h2
  apply tm_two_cn_algebra n (dist u a ^ 2) (dist u b ^ 2) (dist a b ^ 2)
    (dist v b ^ 2) _ (by linarith)
  · convert h1 using 1
    dsimp [s, sp]
    field_simp
  · convert h2 using 1
    dsimp [sp]
    field_simp

theorem tm_increment_step (G : Geometry X) (u a b c : X) (n : ℝ) (hn : 4 ≤ n)
    (hne : dist b c ≤
      dist (G.mix ((n - 3) / (n - 1)) u a) (G.mix ((n - 2) / n) u b))
    (hprev : dist a b ≤ dist u a / (n - 1)) : dist b c ≤ dist u b / n := by
  apply tm_increment_algebra n (dist u a) (dist u b) (dist a b) (dist b c) hn
    dist_nonneg dist_nonneg dist_nonneg dist_nonneg
  · have hne2 : dist b c ^ 2 ≤
        dist (G.mix ((n - 3) / (n - 1)) u a) (G.mix ((n - 2) / n) u b) ^ 2 := by
      gcongr
    exact le_trans hne2 (tm_two_cn G u a b n hn)
  · exact hprev
  · exact dist_triangle u a b

/-- Lemma 4.2, isolated from the indexing of the iteration. -/
theorem tm_anchored_step (G : Geometry X) (u x y : X) (n : ℝ) (hn : 3 ≤ n)
    (hinc : dist x y ≤ dist u x / n) :
    (2 * n - 1) / 3 * dist (G.mix ((n - 2) / n) u x) y ^ 2 ≤
      dist u y ^ 2 - dist u (G.mix ((n - 2) / n) u x) ^ 2 := by
  have hn0 : 0 < n := by linarith
  have hn2 : 0 ≤ n - 2 := by linarith
  let s := (n - 2) / n
  let w := G.mix s u x
  have hs0 : 0 ≤ s := by dsimp [s]; positivity
  have hs1 : s ≤ 1 := by dsimp [s]; apply (div_le_iff₀ hn0).2; linarith
  have hs : 1 - s = 2 / n := by dsimp [s]; field_simp; ring
  have hd : dist u w = s * dist u x := G.dist_left s u x hs0 hs1
  have hdx : dist w x = 2 / n * dist u x := by
    simpa only [hs] using G.dist_right s u x hs0 hs1
  have hr : dist w y ≤ 3 / n * dist u x := by
    have ht := dist_triangle w x y
    rw [hdx] at ht
    have he : 2 / n * dist u x + dist u x / n = 3 / n * dist u x := by ring
    linarith only [ht, hinc, he]
  have hr2 : dist w y ^ 2 ≤ (3 / n * dist u x) ^ 2 := by gcongr
  have hi2 : dist x y ^ 2 ≤ (dist u x / n) ^ 2 := by gcongr
  have hrs : dist w y ^ 2 + 3 * dist x y ^ 2 ≤ 12 / n ^ 2 * dist u x ^ 2 := by
    have he : (3 / n * dist u x) ^ 2 + 3 * (dist u x / n) ^ 2 =
        12 / n ^ 2 * dist u x ^ 2 := by ring
    linarith only [hr2, hi2, he]
  have hcn := G.cn s u x y hs0 hs1
  change dist y w ^ 2 ≤ _ at hcn
  rw [dist_comm y w, dist_comm y u, dist_comm y x, hs] at hcn
  have hcn' : dist w y ^ 2 ≤ 2 / n * dist u y ^ 2
      + (n - 2) / n * dist x y ^ 2 - 2 * (n - 2) / n ^ 2 * dist u x ^ 2 := by
    convert hcn using 1
    dsimp [s]
    field_simp
  have h := tm_anchored_algebra n (dist u x) (dist u y) (dist x y) (dist w y) hn hrs hcn'
  change (2 * n - 1) / 3 * dist w y ^ 2 ≤ dist u y ^ 2 - dist u w ^ 2
  rw [hd, mul_pow]
  exact h

end Cat0Bounds
