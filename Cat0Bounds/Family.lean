import Cat0Bounds.FamilyScalar
import Cat0Bounds.Mann
import Cat0Bounds.Comparison

namespace Cat0Bounds

variable {X : Type*} [MetricSpace X]

noncomputable def familyIter (G : Geometry X) (T : X → X) (u : X) (a l : ℝ) : ℕ → X
  | 0 => mann G T l u
  | k + 1 => mann G T l (G.mix (((k : ℝ) + 1) / (a + (k : ℝ) + 1)) u
      (familyIter G T u a l k))

noncomputable def family (G : Geometry X) (T : X → X) (u : X) (a l : ℝ) : ℕ → X
  | 0 => u
  | k + 1 => G.mix (((k : ℝ) + 1) / (a + (k : ℝ) + 1)) u (familyIter G T u a l k)

noncomputable def familyKappa (a l : ℝ) (k : ℕ) : ℝ := 1 + 2 * l * (k : ℝ) / (a + 1)

theorem familyIter_eq_mann (G : Geometry X) (T : X → X) (u : X) (a l : ℝ) (k : ℕ) :
    familyIter G T u a l k = mann G T l (family G T u a l k) := by
  cases k <;> rfl

theorem family_succ (G : Geometry X) (T : X → X) (u : X) (a l : ℝ) (k : ℕ) :
    family G T u a l (k + 1) =
      G.mix (((k : ℝ) + 1) / (a + (k : ℝ) + 1)) u
        (mann G T l (family G T u a l k)) := by
  rw [family, familyIter_eq_mann]

theorem familyKappa_pos (a l : ℝ) (ha : 1 ≤ a) (hl : 0 ≤ l) (k : ℕ) :
    0 < familyKappa a l k := by
  have hap : 0 < a + 1 := by linarith
  unfold familyKappa
  positivity

theorem family_two_cn (G : Geometry X) (u x y : X) (a n : ℝ)
    (ha : 1 ≤ a) (hn : a + 1 ≤ n) :
    dist (G.mix ((n - a - 1) / (n - 1)) u x) (G.mix ((n - a) / n) u y) ^ 2 ≤
      -a * (n - a - 1) / (n * (n - 1) ^ 2) * dist u x ^ 2
      + a * (n - a) / (n ^ 2 * (n - 1)) * dist u y ^ 2
      + (n - a) * (n - a - 1) / (n * (n - 1)) * dist x y ^ 2 := by
  have hn0 : 0 < n := by linarith
  have hn1 : 0 < n - 1 := by linarith
  have hna : 0 ≤ n - a := by linarith
  have hna1 : 0 ≤ n - a - 1 := by linarith
  let s := (n - a) / n
  let sp := (n - a - 1) / (n - 1)
  let v := G.mix sp u x
  let w := G.mix s u y
  have hs0 : 0 ≤ s := by dsimp [s]; positivity
  have hsp0 : 0 ≤ sp := by dsimp [sp]; positivity
  have hs1 : s ≤ 1 := by dsimp [s]; apply (div_le_iff₀ hn0).2; linarith
  have hsp1 : sp ≤ 1 := by dsimp [sp]; apply (div_le_iff₀ hn1).2; linarith
  have hs : 1 - s = a / n := by dsimp [s]; field_simp; ring
  have hsp : 1 - sp = a / (n - 1) := by dsimp [sp]; field_simp; ring
  have hd : dist u v = sp * dist u x := G.dist_left sp u x hsp0 hsp1
  have h1 := G.cn s u y v hs0 hs1
  have h2 := G.cn sp u x y hsp0 hsp1
  change dist v w ^ 2 ≤ _ at h1
  change dist y v ^ 2 ≤ _ at h2
  rw [dist_comm v u, hd, mul_pow, hs] at h1
  rw [dist_comm y v, dist_comm y u, dist_comm y x, hsp] at h2
  apply family_two_cn_algebra a n (dist u x ^ 2) (dist u y ^ 2) (dist x y ^ 2)
    (dist v y ^ 2) _ ha hn
  · convert h1 using 1
    dsimp [s, sp]
    field_simp
  · convert h2 using 1
    dsimp [sp]
    field_simp

theorem family_increment_step (G : Geometry X) (u x y z : X) (a n : ℝ)
    (ha : 1 ≤ a) (hn : a + 1 ≤ n)
    (hne : dist y z ≤
      dist (G.mix ((n - a - 1) / (n - 1)) u x) (G.mix ((n - a) / n) u y))
    (hprev : dist x y ≤ dist u x / (n - 1)) : dist y z ≤ dist u y / n := by
  apply family_increment_algebra a n (dist u x) (dist u y) (dist x y) (dist y z)
    ha hn dist_nonneg dist_nonneg dist_nonneg
  · have hne2 : dist y z ^ 2 ≤
        dist (G.mix ((n - a - 1) / (n - 1)) u x) (G.mix ((n - a) / n) u y) ^ 2 := by
      gcongr
    exact le_trans hne2 (family_two_cn G u x y a n ha hn)
  · exact hprev
  · exact dist_triangle u x y

theorem family_increment_of_recurrence (G : Geometry X) {S : X → X}
    (hS : LipschitzWith 1 S) (u : X) (a : ℝ) (ha : 1 ≤ a) (x : ℕ → X)
    (h0 : x 0 = S u)
    (hstep : ∀ k : ℕ, x (k + 1) =
      S (G.mix (((k : ℝ) + 1) / (a + (k : ℝ) + 1)) u (x k)))
    (k : ℕ) : dist (x k) (x (k + 1)) ≤ dist u (x k) / (a + (k : ℝ) + 1) := by
  induction k with
  | zero =>
    have hap : 0 < a + 1 := by linarith
    have hs0 : 0 ≤ 1 / (a + 1) := by positivity
    have hs1 : 1 / (a + 1) ≤ 1 := by apply (div_le_iff₀ hap).2; linarith
    have hd := G.dist_left (1 / (a + 1)) u (x 0) hs0 hs1
    have hne := nonexpansive_dist hS u (G.mix (1 / (a + 1)) u (x 0))
    have he : x 1 = S (G.mix (1 / (a + 1)) u (x 0)) := by simpa using hstep 0
    rw [← h0, ← he, hd] at hne
    simpa only [Nat.cast_zero, add_zero, zero_add, one_div_mul_eq_div] using hne
  | succ k ih =>
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hn : a + 1 ≤ a + (k : ℝ) + 2 := by linarith
    have he1 : (a + (k : ℝ) + 2 - a - 1) / (a + (k : ℝ) + 2 - 1) =
        ((k : ℝ) + 1) / (a + (k : ℝ) + 1) := by congr 1 <;> ring
    have he2 : (a + (k : ℝ) + 2 - a) / (a + (k : ℝ) + 2) =
        (((k + 1 : ℕ) : ℝ) + 1) / (a + ((k + 1 : ℕ) : ℝ) + 1) := by
      push_cast
      congr 1 <;> ring
    have hne : dist (x (k + 1)) (x ((k + 1) + 1)) ≤
        dist (G.mix ((a + (k : ℝ) + 2 - a - 1) / (a + (k : ℝ) + 2 - 1)) u (x k))
          (G.mix ((a + (k : ℝ) + 2 - a) / (a + (k : ℝ) + 2)) u (x (k + 1))) := by
      rw [he1, he2]
      calc
        _ = dist (S (G.mix (((k : ℝ) + 1) / (a + (k : ℝ) + 1)) u (x k)))
            (S (G.mix ((((k + 1 : ℕ) : ℝ) + 1) / (a + ((k + 1 : ℕ) : ℝ) + 1))
              u (x (k + 1)))) := congrArg₂ dist (hstep k) (hstep (k + 1))
        _ ≤ _ := nonexpansive_dist hS _ _
    have hprev : dist (x k) (x (k + 1)) ≤ dist u (x k) / (a + (k : ℝ) + 2 - 1) := by
      convert ih using 1
      congr 1
      ring
    have h := family_increment_step G u (x k) (x (k + 1)) (x ((k + 1) + 1))
      a (a + (k : ℝ) + 2) ha hn hne hprev
    convert h using 1
    push_cast
    ring

theorem family_increment (G : Geometry X) {T : X → X} (hT : LipschitzWith 1 T)
    (u : X) (a l : ℝ) (ha : 1 ≤ a) (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (k : ℕ) :
    dist (familyIter G T u a l k) (familyIter G T u a l (k + 1))
      ≤ dist u (familyIter G T u a l k) / (a + (k : ℝ) + 1) :=
  family_increment_of_recurrence G (mann_nonexpansive G hT l hl0 hl1) u a ha
    (familyIter G T u a l) rfl (fun _ => rfl) k

theorem family_anchored_step (G : Geometry X) (u x y : X) (a n : ℝ)
    (ha : 1 ≤ a) (hn : a ≤ n) (hinc : dist x y ≤ dist u x / n) :
    (2 * n - a + 1) / (a + 1) * dist (G.mix ((n - a) / n) u x) y ^ 2 ≤
      dist u y ^ 2 - dist u (G.mix ((n - a) / n) u x) ^ 2 := by
  have ha0 : 0 < a := by linarith
  have hap : 0 < a + 1 := by linarith
  have ham : 0 ≤ a - 1 := by linarith
  have hn0 : 0 < n := by linarith
  have hna : 0 ≤ n - a := by linarith
  let s := (n - a) / n
  let w := G.mix s u x
  have hs0 : 0 ≤ s := by dsimp [s]; positivity
  have hs1 : s ≤ 1 := by dsimp [s]; apply (div_le_iff₀ hn0).2; linarith
  have hs : 1 - s = a / n := by dsimp [s]; field_simp; ring
  have hd : dist u w = s * dist u x := G.dist_left s u x hs0 hs1
  have hdx : dist w x = a / n * dist u x := by
    simpa only [hs] using G.dist_right s u x hs0 hs1
  have hr : dist w y ≤ (a + 1) / n * dist u x := by
    have ht := dist_triangle w x y
    rw [hdx] at ht
    have he : a / n * dist u x + dist u x / n = (a + 1) / n * dist u x := by ring
    linarith only [ht, hinc, he]
  have hr2 : dist w y ^ 2 ≤ ((a + 1) / n * dist u x) ^ 2 := by gcongr
  have hi2 : dist x y ^ 2 ≤ (dist u x / n) ^ 2 := by gcongr
  have hrs : dist x y ^ 2 + (a - 1) / (a + 1) * dist w y ^ 2
      ≤ a ^ 2 / n ^ 2 * dist u x ^ 2 := by
    have hm := mul_le_mul_of_nonneg_left hr2 (show 0 ≤ (a - 1) / (a + 1) by positivity)
    have he : (dist u x / n) ^ 2 + (a - 1) / (a + 1) * ((a + 1) / n * dist u x) ^ 2
        = a ^ 2 / n ^ 2 * dist u x ^ 2 := by field_simp; ring
    linarith only [hm, hi2, he]
  have hcn := G.cn s u x y hs0 hs1
  change dist y w ^ 2 ≤ _ at hcn
  rw [dist_comm y w, dist_comm y u, dist_comm y x, hs] at hcn
  have hcn' : dist w y ^ 2 ≤ a / n * dist u y ^ 2
      + (n - a) / n * dist x y ^ 2 - a * (n - a) / n ^ 2 * dist u x ^ 2 := by
    convert hcn using 1
    dsimp [s]
    field_simp
  have h := family_anchored_algebra a n (dist u x) (dist u y) (dist x y) (dist w y)
    ha hn hrs hcn'
  change (2 * n - a + 1) / (a + 1) * dist w y ^ 2 ≤ dist u y ^ 2 - dist u w ^ 2
  rw [hd, mul_pow]
  exact h

theorem family_anchored (G : Geometry X) {T : X → X} (hT : LipschitzWith 1 T)
    (u : X) (a l : ℝ) (ha : 1 ≤ a) (hl0 : 0 < l) (hl1 : l ≤ 1) (k : ℕ) :
    familyKappa a l k * dist (family G T u a l k) (T (family G T u a l k)) ^ 2
      ≤ dist u (T (family G T u a l k)) ^ 2 - dist u (family G T u a l k) ^ 2 := by
  cases k with
  | zero => simp [family, familyKappa]
  | succ k =>
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hap : 0 < a + 1 := by linarith
    have hn : a ≤ a + (k : ℝ) + 1 := by linarith
    have he : (a + (k : ℝ) + 1 - a) / (a + (k : ℝ) + 1) =
        ((k : ℝ) + 1) / (a + (k : ℝ) + 1) := by congr 1; ring
    have h := family_anchored_step G u (familyIter G T u a l k)
      (familyIter G T u a l (k + 1)) a (a + (k : ℝ) + 1) ha hn
      (family_increment G hT u a l ha (le_of_lt hl0) hl1 k)
    rw [he] at h
    change (2 * (a + (k : ℝ) + 1) - a + 1) / (a + 1) *
        dist (family G T u a l (k + 1)) (familyIter G T u a l (k + 1)) ^ 2
      ≤ dist u (familyIter G T u a l (k + 1)) ^ 2
        - dist u (family G T u a l (k + 1)) ^ 2 at h
    rw [familyIter_eq_mann] at h
    have ht := mann_anchored_transfer G T u (family G T u a l (k + 1))
      l ((2 * (a + (k : ℝ) + 1) - a + 1) / (a + 1)) hl0 hl1 h
    convert ht using 1
    unfold familyKappa
    push_cast
    congr 1
    field_simp
    ring

theorem family_radius (G : Geometry X) {T : X → X} (hT : LipschitzWith 1 T)
    (u p : X) (a l : ℝ) (ha : 1 ≤ a) (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (k : ℕ) :
    dist p (family G T u a l k) ≤ dist u p + l * (k : ℝ) / (a + 1) * dist p (T p) := by
  have hap : 0 < a + 1 := by linarith
  induction k with
  | zero => simp [family, dist_comm p u]
  | succ k ih =>
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hd : 0 < a + (k : ℝ) + 1 := by linarith
    let s : ℝ := ((k : ℝ) + 1) / (a + (k : ℝ) + 1)
    let z := family G T u a l k
    have hs0 : 0 ≤ s := by dsimp [s]; positivity
    have hs1 : s ≤ 1 := by dsimp [s]; apply (div_le_iff₀ hd).2; linarith
    have him : dist p (T z) ≤ dist p (T p) + dist p z := by
      exact le_trans (dist_triangle p (T p) (T z))
        (add_le_add_right (nonexpansive_dist hT p z) _)
    have hym := convex_distance G l z (T z) p hl0 hl1
    change dist p (mann G T l z) ≤ _ at hym
    have hy : dist p (mann G T l z) ≤ dist p z + l * dist p (T p) := by
      have hm := mul_le_mul_of_nonneg_left him hl0
      linarith only [hym, hm]
    have hz := convex_distance G s u (mann G T l z) p hs0 hs1
    rw [dist_comm p u] at hz
    have hfamily : family G T u a l (k + 1) = G.mix s u (mann G T l z) :=
      family_succ G T u a l k
    rw [← hfamily] at hz
    have hy' : dist p (mann G T l z) ≤
        dist u p + l * (k : ℝ) / (a + 1) * dist p (T p) + l * dist p (T p) := by
      exact le_trans hy (add_le_add_left ih _)
    calc
      _ ≤ (1 - s) * dist u p + s * (dist u p + l * (k : ℝ) / (a + 1) * dist p (T p)
          + l * dist p (T p)) := by
        have hm := mul_le_mul_of_nonneg_left hy' hs0
        linarith only [hz, hm]
      _ = _ := by
        dsimp [s]
        push_cast
        field_simp
        ring

theorem family_bound (G : Geometry X) {T : X → X} (hT : LipschitzWith 1 T)
    (u p : X) (a l : ℝ) (ha : 1 ≤ a) (hl0 : 0 < l) (hl1 : l ≤ 1) (k : ℕ) :
    dist (family G T u a l k) (T (family G T u a l k))
      ≤ dist p (T p) + 2 * dist u p / familyKappa a l k := by
  apply endpoint_comparison G hT u (family G T u a l k) p (familyKappa a l k)
    (familyKappa_pos a l ha (le_of_lt hl0) k)
    (family_anchored G hT u a l ha hl0 hl1 k)
  convert family_radius G hT u p a l ha (le_of_lt hl0) hl1 k using 1
  unfold familyKappa
  ring

theorem family_fixed_bound (G : Geometry X) {T : X → X} (hT : LipschitzWith 1 T)
    {p : X} (hp : T p = p) (u : X) (a l : ℝ)
    (ha : 1 ≤ a) (hl0 : 0 < l) (hl1 : l ≤ 1) (k : ℕ) :
    dist (family G T u a l k) (T (family G T u a l k))
      ≤ 2 * dist u p / familyKappa a l k := by
  simpa only [hp, dist_self, zero_add] using family_bound G hT u p a l ha hl0 hl1 k

theorem family_endpoint_bound (G : Geometry X) {T : X → X} (hT : LipschitzWith 1 T)
    (u p : X) (a l : ℝ) (ha : 1 ≤ a) (hl0 : 0 < l) (hl1 : l ≤ 1) (k : ℕ) :
    dist (familyIter G T u a l k) (T (familyIter G T u a l k))
      ≤ dist p (T p) + 2 * dist u p / familyKappa a l k := by
  rw [familyIter_eq_mann]
  exact le_trans (mann_residual G hT l (le_of_lt hl0) hl1 _)
    (family_bound G hT u p a l ha hl0 hl1 k)

end Cat0Bounds
