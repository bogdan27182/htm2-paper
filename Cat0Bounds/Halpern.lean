import Cat0Bounds.Geometry
import Cat0Bounds.Scalar

namespace Cat0Bounds

variable {X : Type*} [MetricSpace X]

noncomputable def halpern (G : Geometry X) (T : X → X) (u : X) : ℕ → X
  | 0 => u
  | k + 1 => G.mix (((k : ℝ) + 1) / ((k : ℝ) + 2)) u (T (halpern G T u k))

noncomputable def halpernPotential (G : Geometry X) (T : X → X) (u : X) (k : ℕ) : ℝ :=
  ((k : ℝ) + 1) ^ 2 * dist (halpern G T u k) (T (halpern G T u k)) ^ 2
    + ((k : ℝ) + 1) *
      (dist u (halpern G T u k) ^ 2 - dist u (T (halpern G T u k)) ^ 2)

/-- Lemma 3.1: the Halpern potential decreases at each step. -/
theorem halpernPotential_step (G : Geometry X) {T : X → X}
    (hT : LipschitzWith 1 T) (u : X) (k : ℕ) :
    halpernPotential G T u (k + 1) ≤ halpernPotential G T u k := by
  let x := halpern G T u
  let s : ℝ := ((k : ℝ) + 1) / ((k : ℝ) + 2)
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hk2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
  have hs0 : 0 ≤ s := by dsimp [s]; positivity
  have hs1 : s ≤ 1 := by
    dsimp [s]
    apply (div_le_iff₀ hk2).2
    linarith
  have hx : x (k + 1) = G.mix s u (T (x k)) := rfl
  have hne : dist (T (x k)) (T (x (k + 1))) ≤ dist (x k) (G.mix s u (T (x k))) := by
    rw [← hx]
    exact nonexpansive_dist hT _ _
  have hcs := two_cn G u (x k) (T (x k)) (T (x (k + 1))) s hs0 hs1 hne
  rw [← hx] at hcs
  have hsplit : 1 - s = 1 / ((k : ℝ) + 2) := by
    dsimp [s]
    field_simp
    ring
  rw [hsplit] at hcs
  have hd := G.dist_left s u (T (x k)) hs0 hs1
  rw [← hx] at hd
  have ha := halpern_algebra (k : ℝ)
    (dist (x k) (T (x k)) ^ 2) (dist (x (k + 1)) (T (x (k + 1))) ^ 2)
    (dist u (x k) ^ 2) (dist u (T (x k)) ^ 2)
    (dist u (T (x (k + 1))) ^ 2) hk hcs
  change ((k + 1 : ℕ) + 1 : ℝ) ^ 2 * dist (x (k + 1)) (T (x (k + 1))) ^ 2
      + ((k + 1 : ℕ) + 1 : ℝ) *
        (dist u (x (k + 1)) ^ 2 - dist u (T (x (k + 1))) ^ 2)
    ≤ ((k : ℝ) + 1) ^ 2 * dist (x k) (T (x k)) ^ 2
      + ((k : ℝ) + 1) * (dist u (x k) ^ 2 - dist u (T (x k)) ^ 2)
  rw [hd, mul_pow]
  convert ha using 1
  push_cast
  dsimp [s]
  ring

theorem halpernPotential_nonpos (G : Geometry X) {T : X → X}
    (hT : LipschitzWith 1 T) (u : X) (N : ℕ) : halpernPotential G T u N ≤ 0 := by
  induction N with
  | zero => simp [halpernPotential, halpern]
  | succ k ih => exact le_trans (halpernPotential_step G hT u k) ih

/-- The anchored estimate before the use of the fixed point. -/
theorem halpern_anchored (G : Geometry X) {T : X → X}
    (hT : LipschitzWith 1 T) (u : X) (N : ℕ) :
    ((N : ℝ) + 1) * dist (halpern G T u N) (T (halpern G T u N)) ^ 2
      ≤ dist u (T (halpern G T u N)) ^ 2 - dist u (halpern G T u N) ^ 2 := by
  have h := halpernPotential_nonpos G hT u N
  unfold halpernPotential at h
  have hn : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  by_contra hnle
  have hpos : 0 < ((N : ℝ) + 1) * dist (halpern G T u N) (T (halpern G T u N)) ^ 2
      - (dist u (T (halpern G T u N)) ^ 2 - dist u (halpern G T u N) ^ 2) :=
    sub_pos.mpr (lt_of_not_ge hnle)
  have := mul_pos hn hpos
  nlinarith

/-- The upper bound in Theorem 1.1, for all horizons including zero. -/
theorem halpern_bound (G : Geometry X) {T : X → X} (hT : LipschitzWith 1 T)
    {p : X} (hp : T p = p) (u : X) (N : ℕ) :
    dist (halpern G T u N) (T (halpern G T u N)) ≤ 2 * dist u p / ((N : ℝ) + 1) := by
  apply residual_of_sq _ _ _ dist_nonneg dist_nonneg (by positivity)
  exact le_trans (halpern_anchored G hT u N) (endpoint G hT hp u _)

end Cat0Bounds
