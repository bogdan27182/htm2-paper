import Cat0Bounds.Comparison
import Cat0Bounds.Sharpness

/-! Adaptive anchoring, including the stopping convention.

The quotient adaptiveCoeff is a total real-valued expression. Its value
at a fixed point is irrelevant: adaptiveStep stops before using it, and
all coefficient statements below explicitly assume a nonfixed iterate.
-/

namespace Cat0Bounds

variable {X : Type*} [MetricSpace X]

def anchoredPhi (T : X → X) (u z : X) : ℝ :=
  dist u (T z) ^ 2 - dist u z ^ 2

noncomputable def adaptiveCoeff (T : X → X) (u z : X) : ℝ :=
  anchoredPhi T u z / dist z (T z) ^ 2

noncomputable def adaptiveStep (G : Geometry X) (T : X → X) (u z : X) : X := by
  classical
  exact if T z = z then z
    else G.mix (adaptiveCoeff T u z / (adaptiveCoeff T u z + 1)) u (T z)

noncomputable def adaptive (G : Geometry X) (T : X → X) (u : X) : ℕ → X
  | 0 => u
  | k + 1 => adaptiveStep G T u (adaptive G T u k)

theorem adaptiveStep_of_fixed (G : Geometry X) (T : X → X) (u z : X)
    (hz : T z = z) : adaptiveStep G T u z = z := by
  classical
  simp [adaptiveStep, hz]

theorem adaptiveStep_of_nonfixed (G : Geometry X) (T : X → X) (u z : X)
    (hz : T z ≠ z) :
    adaptiveStep G T u z =
      G.mix (adaptiveCoeff T u z / (adaptiveCoeff T u z + 1)) u (T z) := by
  classical
  simp [adaptiveStep, hz]

theorem adaptiveCoeff_mul (T : X → X) (u z : X) (hz : T z ≠ z) :
    adaptiveCoeff T u z * dist z (T z) ^ 2 = anchoredPhi T u z := by
  have hr : 0 < dist z (T z) := dist_pos.mpr (Ne.symm hz)
  unfold adaptiveCoeff
  exact div_mul_cancel₀ _ (ne_of_gt (sq_pos_of_pos hr))

theorem adaptiveCoeff_initial (T : X → X) (u : X) (hu : T u ≠ u) :
    adaptiveCoeff T u u = 1 := by
  have hr : 0 < dist u (T u) := dist_pos.mpr (Ne.symm hu)
  simp [adaptiveCoeff, anchoredPhi, ne_of_gt (sq_pos_of_pos hr)]

/-- The two-CN anchored-step inequality; it needs no fixed point. -/
theorem anchored_step (G : Geometry X) {T : X → X} (hT : LipschitzWith 1 T)
    (u z : X) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    dist (G.mix s u (T z)) (T (G.mix s u (T z))) ^ 2
        - (1 - s) * anchoredPhi T u (G.mix s u (T z))
      ≤ s * (s * dist z (T z) ^ 2 - (1 - s) * anchoredPhi T u z) := by
  have hne := nonexpansive_dist hT z (G.mix s u (T z))
  have hc := two_cn G u z (T z) (T (G.mix s u (T z))) s hs0 hs1 hne
  have hd := G.dist_left s u (T z) hs0 hs1
  unfold anchoredPhi
  rw [hd, mul_pow]
  nlinarith only [hc]

/-- At every positive-coefficient step, the next anchored inequality
holds even when the next point is fixed. -/
theorem adaptiveStep_anchored (G : Geometry X) {T : X → X}
    (hT : LipschitzWith 1 T) (u z : X) (hz : T z ≠ z)
    (hφ : 0 < adaptiveCoeff T u z) :
    (adaptiveCoeff T u z + 1) *
        dist (adaptiveStep G T u z) (T (adaptiveStep G T u z)) ^ 2
      ≤ anchoredPhi T u (adaptiveStep G T u z) := by
  let φ := adaptiveCoeff T u z
  let s := φ / (φ + 1)
  have hφ0 : 0 < φ := hφ
  have hden : 0 < φ + 1 := by linarith
  have hs0 : 0 ≤ s := by dsimp [s]; positivity
  have hs1 : s ≤ 1 := by
    dsimp [s]
    apply (div_le_iff₀ hden).2
    linarith
  have hx : adaptiveStep G T u z = G.mix s u (T z) :=
    adaptiveStep_of_nonfixed G T u z hz
  have hc := anchored_step G hT u z s hs0 hs1
  have hPhi : φ * dist z (T z) ^ 2 = anchoredPhi T u z :=
    adaptiveCoeff_mul T u z hz
  have hzero : s * (s * dist z (T z) ^ 2 -
      (1 - s) * anchoredPhi T u z) = 0 := by
    rw [← hPhi]
    dsimp [s]
    field_simp [ne_of_gt hden]
    ring
  rw [hzero] at hc
  have hm := mul_le_mul_of_nonneg_left hc (le_of_lt hden)
  have hcancel : (φ + 1) * (1 - s) = 1 := by
    dsimp [s]
    field_simp [ne_of_gt hden]
    ring
  rw [hx]
  change (φ + 1) * dist (G.mix s u (T z)) (T (G.mix s u (T z))) ^ 2
    ≤ anchoredPhi T u (G.mix s u (T z))
  rw [mul_sub, ← mul_assoc, hcancel, mul_zero, one_mul] at hm
  linarith only [hm]

theorem adaptiveStep_coeff_growth (G : Geometry X) {T : X → X}
    (hT : LipschitzWith 1 T) (u z : X) (hz : T z ≠ z)
    (hφ : 0 < adaptiveCoeff T u z)
    (hnext : T (adaptiveStep G T u z) ≠ adaptiveStep G T u z) :
    adaptiveCoeff T u z + 1 ≤ adaptiveCoeff T u (adaptiveStep G T u z) := by
  have ha := adaptiveStep_anchored G hT u z hz hφ
  rw [← adaptiveCoeff_mul T u (adaptiveStep G T u z) hnext] at ha
  have hr : 0 < dist (adaptiveStep G T u z) (T (adaptiveStep G T u z)) :=
    dist_pos.mpr (Ne.symm hnext)
  exact le_of_mul_le_mul_right ha (sq_pos_of_pos hr)

theorem adaptive_stops (G : Geometry X) (T : X → X) (u : X) (k : ℕ)
    (hk : T (adaptive G T u k) = adaptive G T u k) :
    adaptive G T u (k + 1) = adaptive G T u k :=
  adaptiveStep_of_fixed G T u (adaptive G T u k) hk

theorem adaptive_stops_forever (G : Geometry X) (T : X → X) (u : X) (k j : ℕ)
    (hk : T (adaptive G T u k) = adaptive G T u k) :
    adaptive G T u (k + j) = adaptive G T u k := by
  induction j with
  | zero => simp
  | succ j ih =>
      have hfixed : T (adaptive G T u (k + j)) = adaptive G T u (k + j) := by
        rw [ih, hk]
      simpa only [Nat.add_succ] using (adaptive_stops G T u (k + j) hfixed).trans ih

theorem adaptive_nonfixed_of_le (G : Geometry X) (T : X → X) (u : X) {k N : ℕ}
    (hkN : k ≤ N) (hN : T (adaptive G T u N) ≠ adaptive G T u N) :
    T (adaptive G T u k) ≠ adaptive G T u k := by
  intro hk
  have hs := adaptive_stops_forever G T u k (N - k) hk
  rw [Nat.add_sub_of_le hkN] at hs
  exact hN (by rw [hs, hk])

theorem adaptive_nonfixed_previous (G : Geometry X) (T : X → X) (u : X) (k : ℕ)
    (hnext : T (adaptive G T u (k + 1)) ≠ adaptive G T u (k + 1)) :
    T (adaptive G T u k) ≠ adaptive G T u k := by
  intro hk
  have hs := adaptive_stops G T u k hk
  exact hnext (by rw [hs, hk])

/-- Coefficients are at least the iteration index plus one before stopping. -/
theorem adaptiveCoeff_lower (G : Geometry X) {T : X → X} (hT : LipschitzWith 1 T)
    (u : X) (N : ℕ) (hN : T (adaptive G T u N) ≠ adaptive G T u N) :
    (N : ℝ) + 1 ≤ adaptiveCoeff T u (adaptive G T u N) := by
  induction N with
  | zero =>
      simp [adaptive, adaptiveCoeff_initial T u hN]
  | succ k ih =>
      have hk := adaptive_nonfixed_previous G T u k hN
      have hl := ih hk
      have hpos : 0 < adaptiveCoeff T u (adaptive G T u k) := by
        have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        linarith
      have hg := adaptiveStep_coeff_growth G hT u (adaptive G T u k) hk hpos hN
      change (↑(k + 1) : ℝ) + 1 ≤
        adaptiveCoeff T u (adaptiveStep G T u (adaptive G T u k))
      push_cast
      linarith

theorem adaptiveCoeff_growth (G : Geometry X) {T : X → X} (hT : LipschitzWith 1 T)
    (u : X) (k : ℕ) (hnext : T (adaptive G T u (k + 1)) ≠ adaptive G T u (k + 1)) :
    adaptiveCoeff T u (adaptive G T u k) + 1
      ≤ adaptiveCoeff T u (adaptive G T u (k + 1)) := by
  have hk := adaptive_nonfixed_previous G T u k hnext
  have hl := adaptiveCoeff_lower G hT u k hk
  apply adaptiveStep_coeff_growth G hT u (adaptive G T u k) hk _ hnext
  have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  linarith

/-- Every nonstopping update uses an interior geodesic weight. -/
theorem adaptive_weight_admissible (G : Geometry X) {T : X → X}
    (hT : LipschitzWith 1 T) (u : X) (N : ℕ)
    (hN : T (adaptive G T u N) ≠ adaptive G T u N) :
    0 < adaptiveCoeff T u (adaptive G T u N) /
        (adaptiveCoeff T u (adaptive G T u N) + 1) ∧
      adaptiveCoeff T u (adaptive G T u N) /
        (adaptiveCoeff T u (adaptive G T u N) + 1) < 1 := by
  have hl := adaptiveCoeff_lower G hT u N hN
  have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hφ : 0 < adaptiveCoeff T u (adaptive G T u N) := by linarith
  have hden : 0 < adaptiveCoeff T u (adaptive G T u N) + 1 := by linarith
  constructor
  · exact div_pos hφ hden
  · apply (div_lt_iff₀ hden).2
    linarith

/-- Radius propagation relative to an arbitrary comparison point. -/
theorem adaptiveStep_radius (G : Geometry X) {T : X → X} (hT : LipschitzWith 1 T)
    (u z p : X) (hz : T z ≠ z) (hφ : 0 < adaptiveCoeff T u z)
    (hradius : dist p z ≤ dist u p + (adaptiveCoeff T u z - 1) / 2 * dist p (T p)) :
    dist p (adaptiveStep G T u z) ≤
      dist u p + adaptiveCoeff T u z / 2 * dist p (T p) := by
  let φ := adaptiveCoeff T u z
  let s := φ / (φ + 1)
  have hφ0 : 0 < φ := hφ
  have hden : 0 < φ + 1 := by linarith
  have hs0 : 0 ≤ s := by dsimp [s]; positivity
  have hs1 : s ≤ 1 := by
    dsimp [s]
    apply (div_le_iff₀ hden).2
    linarith
  have hTpz : dist p (T z) ≤ dist p z + dist p (T p) := by
    calc
      dist p (T z) ≤ dist p (T p) + dist (T p) (T z) := dist_triangle _ _ _
      _ ≤ dist p (T p) + dist p z := add_le_add le_rfl (nonexpansive_dist hT p z)
      _ = _ := by ring
  rw [adaptiveStep_of_nonfixed G T u z hz]
  calc
    dist p (G.mix s u (T z)) ≤ (1 - s) * dist p u + s * dist p (T z) :=
      convex_distance G s u (T z) p hs0 hs1
    _ ≤ (1 - s) * dist p u +
        s * (dist u p + (φ - 1) / 2 * dist p (T p) + dist p (T p)) := by
      apply add_le_add le_rfl
      apply mul_le_mul_of_nonneg_left _ hs0
      exact le_trans hTpz (add_le_add hradius le_rfl)
    _ = dist u p + φ / 2 * dist p (T p) := by
      rw [dist_comm p u]
      dsimp [s]
      field_simp [ne_of_gt hden]
      ring

theorem adaptive_radius (G : Geometry X) {T : X → X} (hT : LipschitzWith 1 T)
    (u p : X) (N : ℕ) (hN : T (adaptive G T u N) ≠ adaptive G T u N) :
    dist p (adaptive G T u N) ≤
      dist u p + (adaptiveCoeff T u (adaptive G T u N) - 1) / 2 * dist p (T p) := by
  induction N with
  | zero =>
      simp only [adaptive] at *
      rw [adaptiveCoeff_initial T u hN]
      simp [dist_comm]
  | succ k ih =>
      have hk := adaptive_nonfixed_previous G T u k hN
      have hl := adaptiveCoeff_lower G hT u k hk
      have hpos : 0 < adaptiveCoeff T u (adaptive G T u k) := by
        have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        linarith
      have hs := adaptiveStep_radius G hT u (adaptive G T u k) p hk hpos (ih hk)
      have hg := adaptiveCoeff_growth G hT u k hN
      change dist p (adaptiveStep G T u (adaptive G T u k)) ≤ _
      calc
        _ ≤ dist u p + adaptiveCoeff T u (adaptive G T u k) / 2 * dist p (T p) := hs
        _ ≤ _ := by
          gcongr
          linarith

/-- The adaptive comparison bound at a nonfixed iterate. -/
theorem adaptive_comparison_bound (G : Geometry X) {T : X → X}
    (hT : LipschitzWith 1 T) (u p : X) (N : ℕ)
    (hN : T (adaptive G T u N) ≠ adaptive G T u N) :
    dist (adaptive G T u N) (T (adaptive G T u N)) ≤
      dist p (T p) + 2 * dist u p / adaptiveCoeff T u (adaptive G T u N) := by
  have hl := adaptiveCoeff_lower G hT u N hN
  have hpos : 0 < adaptiveCoeff T u (adaptive G T u N) := by
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    linarith
  apply endpoint_comparison G hT u (adaptive G T u N) p
    (adaptiveCoeff T u (adaptive G T u N)) hpos
  · exact le_of_eq (adaptiveCoeff_mul T u (adaptive G T u N) hN)
  · exact adaptive_radius G hT u p N hN

/-- The horizon bound remains valid after the iteration has stopped. -/
theorem adaptive_horizon_bound (G : Geometry X) {T : X → X}
    (hT : LipschitzWith 1 T) (u p : X) (N : ℕ) :
    dist (adaptive G T u N) (T (adaptive G T u N)) ≤
      dist p (T p) + 2 * dist u p / ((N : ℝ) + 1) := by
  by_cases hN : T (adaptive G T u N) = adaptive G T u N
  · rw [hN, dist_self]
    positivity
  · have hb := adaptive_comparison_bound G hT u p N hN
    have hl := adaptiveCoeff_lower G hT u N hN
    refine le_trans hb (add_le_add le_rfl ?_)
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) hl

theorem adaptive_fixed_point_bound (G : Geometry X) {T : X → X}
    (hT : LipschitzWith 1 T) {p : X} (hp : T p = p) (u : X) (N : ℕ) :
    dist (adaptive G T u N) (T (adaptive G T u N)) ≤
      2 * dist u p / ((N : ℝ) + 1) := by
  simpa [hp] using adaptive_horizon_bound G hT u p N

/-- On the extremizer's translation branch, the adaptive coefficient is
exactly the coefficient of ordinary Halpern iteration. -/
theorem extremizer_adaptiveCoeff (q : ℝ) (hq : 0 < q) (k : ℕ)
    (hbranch : ((k : ℝ) + 1) * q ≤ 2) :
    adaptiveCoeff (extremizer q) (-1) (-1 + (k : ℝ) * q / 2) = (k : ℝ) + 1 := by
  have ht : -1 + (k : ℝ) * q / 2 ≤ -q / 2 := by linarith only [hbranch]
  unfold adaptiveCoeff anchoredPhi
  rw [extremizer_left q _ ht]
  simp only [Real.dist_eq, sq_abs]
  have hnum :
      (-1 - (-1 + (k : ℝ) * q / 2 + q)) ^ 2
        - (-1 - (-1 + (k : ℝ) * q / 2)) ^ 2 = ((k : ℝ) + 1) * q ^ 2 := by ring
  have hden : (-1 + (k : ℝ) * q / 2 - (-1 + (k : ℝ) * q / 2 + q)) ^ 2 = q ^ 2 := by
    ring
  rw [hnum, hden]
  field_simp [ne_of_gt hq]

theorem adaptive_eq_halpern_extremizer (q : ℝ) (hq : 0 < q) (k : ℕ)
    (hbranch : ((k : ℝ) + 1) * q ≤ 2) :
    adaptive realGeometry (extremizer q) (-1) k =
      halpern realGeometry (extremizer q) (-1) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have hk : ((k : ℝ) + 1) * q ≤ 2 := by
        push_cast at hbranch
        nlinarith only [hbranch, hq]
      have ht : -1 + (k : ℝ) * q / 2 ≤ -q / 2 := by linarith only [hk]
      have horbit := halpern_orbit q (le_of_lt hq) k hk
      have hnonfixed : extremizer q (halpern realGeometry (extremizer q) (-1) k) ≠
          halpern realGeometry (extremizer q) (-1) k := by
        rw [horbit, extremizer_left q _ ht]
        linarith
      have hcoeff :
          adaptiveCoeff (extremizer q) (-1) (halpern realGeometry (extremizer q) (-1) k)
            = (k : ℝ) + 1 := by
        rw [horbit]
        exact extremizer_adaptiveCoeff q hq k hk
      change adaptiveStep realGeometry (extremizer q) (-1)
          (adaptive realGeometry (extremizer q) (-1) k) =
        realGeometry.mix (((k : ℝ) + 1) / ((k : ℝ) + 2)) (-1)
          (extremizer q (halpern realGeometry (extremizer q) (-1) k))
      rw [ih hk, adaptiveStep_of_nonfixed _ _ _ _ hnonfixed, hcoeff]
      congr 1
      ring

theorem adaptive_sharp (N : ℕ) :
    let q := 2 / ((N : ℝ) + 1)
    adaptiveCoeff (extremizer q) (-1) (adaptive realGeometry (extremizer q) (-1) N)
        = (N : ℝ) + 1 ∧
      dist (adaptive realGeometry (extremizer q) (-1) N)
        (extremizer q (adaptive realGeometry (extremizer q) (-1) N)) = q := by
  dsimp only
  let q := 2 / ((N : ℝ) + 1)
  have hn : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hq : 0 < q := by dsimp [q]; positivity
  have hprod : ((N : ℝ) + 1) * q = 2 := by dsimp [q]; field_simp
  have heq := adaptive_eq_halpern_extremizer q hq N (le_of_eq hprod)
  change adaptiveCoeff (extremizer q) (-1) (adaptive realGeometry (extremizer q) (-1) N)
      = (N : ℝ) + 1 ∧
    dist (adaptive realGeometry (extremizer q) (-1) N)
      (extremizer q (adaptive realGeometry (extremizer q) (-1) N)) = q
  rw [heq]
  constructor
  · rw [halpern_orbit q (le_of_lt hq) N (le_of_eq hprod)]
    exact extremizer_adaptiveCoeff q hq N (le_of_eq hprod)
  · exact halpern_sharp N

/-- Both the coefficient and horizon bounds are attained by a nontrivial
real-line example at each prescribed horizon. -/
theorem adaptive_sharpness (N : ℕ) :
    ∃ T : ℝ → ℝ, LipschitzWith 1 T ∧ T 0 = 0 ∧ dist (-1 : ℝ) 0 = 1 ∧
      adaptiveCoeff T (-1) (adaptive realGeometry T (-1) N) = (N : ℝ) + 1 ∧
      dist (adaptive realGeometry T (-1) N) (T (adaptive realGeometry T (-1) N))
          = 2 / ((N : ℝ) + 1) ∧
      dist (adaptive realGeometry T (-1) N) (T (adaptive realGeometry T (-1) N))
          = 2 / adaptiveCoeff T (-1) (adaptive realGeometry T (-1) N) := by
  let q := 2 / ((N : ℝ) + 1)
  have hsharp := adaptive_sharp N
  dsimp only at hsharp
  refine ⟨extremizer q, extremizer_nonexpansive q, extremizer_fixed q (by dsimp [q]; positivity),
    ?_, hsharp.1, hsharp.2, ?_⟩
  · norm_num [Real.dist_eq]
  · rw [hsharp.1]
    exact hsharp.2

end Cat0Bounds
