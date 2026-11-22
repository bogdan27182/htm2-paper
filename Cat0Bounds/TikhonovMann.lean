import Cat0Bounds.TMGeometry

namespace Cat0Bounds

variable {X : Type*} [MetricSpace X]

/-- The effective orbit, with index `k` corresponding to the paper's `x_{k+3}`. -/
noncomputable def tmIter (G : Geometry X) (T : X → X) (u : X) : ℕ → X
  | 0 => T u
  | k + 1 => T (G.mix (((k : ℝ) + 1) / ((k : ℝ) + 3)) u (tmIter G T u k))

/-- Index `k` corresponds to the paper's `w_{k+2}`. -/
noncomputable def tmShadow (G : Geometry X) (T : X → X) (u : X) : ℕ → X
  | 0 => u
  | k + 1 => G.mix (((k : ℝ) + 1) / ((k : ℝ) + 3)) u (tmIter G T u k)

theorem tmIter_eq_image (G : Geometry X) (T : X → X) (u : X) (k : ℕ) :
    tmIter G T u k = T (tmShadow G T u k) := by
  cases k <;> rfl

/-- Lemma 4.1 for a sequence with the effective Tikhonov–Mann recurrence. -/
theorem tm_increment_of_recurrence (G : Geometry X) {T : X → X}
    (hT : LipschitzWith 1 T) (u : X) (x : ℕ → X) (h0 : x 0 = T u)
    (hstep : ∀ k : ℕ,
      x (k + 1) = T (G.mix (((k : ℝ) + 1) / ((k : ℝ) + 3)) u (x k)))
    (k : ℕ) : dist (x k) (x (k + 1)) ≤ dist u (x k) / ((k : ℝ) + 3) := by
  induction k with
  | zero =>
    have hd := G.dist_left (1 / 3) u (x 0) (by norm_num) (by norm_num)
    have hne := nonexpansive_dist hT u (G.mix (1 / 3) u (x 0))
    have he : x 1 = T (G.mix (1 / 3) u (x 0)) := by simpa using hstep 0
    rw [← h0, ← he, hd] at hne
    simpa only [Nat.cast_zero, zero_add, one_div_mul_eq_div] using hne
  | succ k ih =>
    have hn : (4 : ℝ) ≤ (k : ℝ) + 4 := by have := Nat.cast_nonneg (α := ℝ) k; linarith
    have he1 : ((k : ℝ) + 4 - 3) / ((k : ℝ) + 4 - 1) =
        ((k : ℝ) + 1) / ((k : ℝ) + 3) := by congr 1 <;> ring
    have he2 : ((k : ℝ) + 4 - 2) / ((k : ℝ) + 4) =
        (((k + 1 : ℕ) : ℝ) + 1) / (((k + 1 : ℕ) : ℝ) + 3) := by
      push_cast
      congr 1 <;> ring
    have hne : dist (x (k + 1)) (x ((k + 1) + 1)) ≤
        dist (G.mix (((k : ℝ) + 4 - 3) / ((k : ℝ) + 4 - 1)) u (x k))
          (G.mix (((k : ℝ) + 4 - 2) / ((k : ℝ) + 4)) u (x (k + 1))) := by
      rw [he1, he2]
      calc
        _ = dist (T (G.mix (((k : ℝ) + 1) / ((k : ℝ) + 3)) u (x k)))
            (T (G.mix ((((k + 1 : ℕ) : ℝ) + 1) / (((k + 1 : ℕ) : ℝ) + 3))
              u (x (k + 1)))) := congrArg₂ dist (hstep k) (hstep (k + 1))
        _ ≤ _ := nonexpansive_dist hT _ _
    have hprev : dist (x k) (x (k + 1)) ≤ dist u (x k) / ((k : ℝ) + 4 - 1) := by
      convert ih using 1
      congr 1
      ring
    have h := tm_increment_step G u (x k) (x (k + 1)) (x ((k + 1) + 1))
      ((k : ℝ) + 4) hn hne hprev
    convert h using 1
    push_cast
    ring

theorem tm_increment (G : Geometry X) {T : X → X} (hT : LipschitzWith 1 T)
    (u : X) (k : ℕ) :
    dist (tmIter G T u k) (tmIter G T u (k + 1))
      ≤ dist u (tmIter G T u k) / ((k : ℝ) + 3) :=
  tm_increment_of_recurrence G hT u (tmIter G T u) rfl (fun _ => rfl) k

/-- The shadow residual bound with shifted indexing, including `w₂ = u`. -/
theorem tm_shadow_bound (G : Geometry X) {T : X → X} (hT : LipschitzWith 1 T)
    {p : X} (hp : T p = p) (u : X) (k : ℕ) :
    dist (tmShadow G T u k) (T (tmShadow G T u k))
      ≤ 6 * dist u p / (2 * (k : ℝ) + 3) := by
  cases k with
  | zero =>
    have ht := dist_triangle u p (T u)
    have hn : dist p (T u) ≤ dist u p := by
      simpa only [hp, dist_comm p u] using nonexpansive_dist hT p u
    simp only [tmShadow, Nat.cast_zero, mul_zero, zero_add]
    linarith only [ht, hn]
  | succ k =>
    have hn : (3 : ℝ) ≤ (k : ℝ) + 3 := by have := Nat.cast_nonneg (α := ℝ) k; linarith
    have he : ((k : ℝ) + 3 - 2) / ((k : ℝ) + 3) =
        ((k : ℝ) + 1) / ((k : ℝ) + 3) := by congr 1; ring
    have h := tm_anchored_step G u (tmIter G T u k) (tmIter G T u (k + 1))
      ((k : ℝ) + 3) hn (tm_increment G hT u k)
    rw [he] at h
    change (2 * ((k : ℝ) + 3) - 1) / 3 *
        dist (tmShadow G T u (k + 1)) (tmIter G T u (k + 1)) ^ 2
      ≤ dist u (tmIter G T u (k + 1)) ^ 2 - dist u (tmShadow G T u (k + 1)) ^ 2 at h
    rw [tmIter_eq_image] at h
    have hkappa : 0 < (2 * ((k : ℝ) + 3) - 1) / 3 := by
      apply div_pos _ (by norm_num)
      linarith
    have hb := residual_of_sq _ _ _ dist_nonneg dist_nonneg hkappa
      (le_trans h (endpoint G hT hp u _))
    have heq : 2 * dist u p / ((2 * ((k : ℝ) + 3) - 1) / 3) =
        6 * dist u p / (2 * (k : ℝ) + 5) := by
      have hd : 2 * ((k : ℝ) + 3) - 1 = 2 * (k : ℝ) + 5 := by ring
      rw [hd]
      field_simp
      ring
    rw [heq] at hb
    simpa only [Nat.cast_add, Nat.cast_one,
      show 2 * ((k : ℝ) + 1) + 3 = 2 * (k : ℝ) + 5 by ring] using hb

/-- The paper's `w_N` for `N ≥ 2`. Values below 2 are auxiliary. -/
noncomputable def tmW (G : Geometry X) (T : X → X) (u : X) (N : ℕ) : X :=
  tmShadow G T u (N - 2)

/-- The paper's `x_n` for `n ≥ 3`. Values below 3 are auxiliary. -/
noncomputable def tmX (G : Geometry X) (T : X → X) (u : X) (n : ℕ) : X :=
  tmIter G T u (n - 3)

theorem tmW_two (G : Geometry X) (T : X → X) (u : X) : tmW G T u 2 = u := rfl

theorem tmX_three (G : Geometry X) (T : X → X) (u : X) : tmX G T u 3 = T u := rfl

/-- The prescribed anchoring coefficient in the original indexing. -/
theorem tm_schedule (G : Geometry X) (T : X → X) (u : X) (N : ℕ) (hN : 3 ≤ N) :
    tmW G T u N = G.mix (((N : ℝ) - 2) / (N : ℝ)) u (tmX G T u N) := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, N = k + 3 := ⟨N - 3, by omega⟩
  subst N
  unfold tmW tmX
  rw [show k + 3 - 2 = k + 1 by omega, Nat.add_sub_cancel]
  rw [tmShadow]
  congr 1
  push_cast
  congr 1
  ring

theorem tm_image (G : Geometry X) (T : X → X) (u : X) (N : ℕ) (hN : 2 ≤ N) :
    tmX G T u (N + 1) = T (tmW G T u N) := by
  unfold tmX tmW
  rw [show N + 1 - 3 = N - 2 by omega]
  exact tmIter_eq_image G T u (N - 2)

/-- Both upper bounds in Theorem 1.2 in the paper's original indexing. -/
theorem tm_bound (G : Geometry X) {T : X → X} (hT : LipschitzWith 1 T)
    {p : X} (hp : T p = p) (u : X) (N : ℕ) (hN : 2 ≤ N) :
    dist (tmX G T u (N + 1)) (T (tmX G T u (N + 1)))
        ≤ dist (tmW G T u N) (T (tmW G T u N)) ∧
      dist (tmW G T u N) (T (tmW G T u N)) ≤ 6 * dist u p / (2 * (N : ℝ) - 1) := by
  constructor
  · rw [tm_image G T u N hN]
    exact nonexpansive_dist hT _ _
  · have h := tm_shadow_bound G hT hp u (N - 2)
    change dist (tmShadow G T u (N - 2)) (T (tmShadow G T u (N - 2))) ≤ _
    convert h using 1
    rw [Nat.cast_sub hN]
    norm_num
    congr 1
    ring

end Cat0Bounds
