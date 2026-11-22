import Cat0Bounds.Halpern
import Cat0Bounds.TikhonovMann
import Cat0Bounds.RealGeometry

namespace Cat0Bounds

/-- The Halpern orbit while it stays on the translation branch. -/
theorem halpern_orbit (q : ℝ) (hq : 0 ≤ q) (k : ℕ)
    (hbranch : ((k : ℝ) + 1) * q ≤ 2) :
    halpern realGeometry (extremizer q) (-1) k = -1 + (k : ℝ) * q / 2 := by
  induction k with
  | zero => simp [halpern]
  | succ k ih =>
    have hk : ((k : ℝ) + 1) * q ≤ 2 := by
      push_cast at hbranch
      nlinarith only [hbranch, hq]
    have ht : -1 + (k : ℝ) * q / 2 ≤ -q / 2 := by linarith only [hk]
    rw [halpern, ih hk, extremizer_left q _ ht]
    simp only [realGeometry]
    have hn : (0 : ℝ) < (k : ℝ) + 2 := by positivity
    push_cast
    field_simp
    ring

/-- Equality in the Halpern residual bound for every horizon. -/
theorem halpern_sharp (N : ℕ) :
    let q := 2 / ((N : ℝ) + 1)
    dist (halpern realGeometry (extremizer q) (-1) N)
      (extremizer q (halpern realGeometry (extremizer q) (-1) N)) = q := by
  dsimp only
  let q := 2 / ((N : ℝ) + 1)
  have hn : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hprod : ((N : ℝ) + 1) * q = 2 := by dsimp [q]; field_simp
  have hx : halpern realGeometry (extremizer q) (-1) N = -q / 2 := by
    rw [halpern_orbit q hq N (le_of_eq hprod)]
    linarith only [hprod]
  change dist (halpern realGeometry (extremizer q) (-1) N)
    (extremizer q (halpern realGeometry (extremizer q) (-1) N)) = q
  rw [hx, extremizer_left q (-q / 2) (le_refl _)]
  rw [Real.dist_eq, show -q / 2 - (-q / 2 + q) = -q by ring,
    abs_neg, abs_of_nonneg hq]

/-- The Tikhonov–Mann shadow orbit on the translation branch. -/
theorem tmShadow_orbit (q : ℝ) (hq : 0 ≤ q) (k : ℕ)
    (hbranch : (2 * (k : ℝ) + 3) * q ≤ 6) :
    tmShadow realGeometry (extremizer q) (-1) k = -1 + (k : ℝ) * q / 3 := by
  induction k with
  | zero => simp [tmShadow]
  | succ k ih =>
    have hk : (2 * (k : ℝ) + 3) * q ≤ 6 := by
      push_cast at hbranch
      nlinarith only [hbranch, hq]
    have ht : -1 + (k : ℝ) * q / 3 ≤ -q / 2 := by linarith only [hk]
    rw [tmShadow, tmIter_eq_image, ih hk, extremizer_left q _ ht]
    simp only [realGeometry]
    have hn : (0 : ℝ) < (k : ℝ) + 3 := by positivity
    push_cast
    field_simp
    ring

/-- Both Tikhonov–Mann residuals are sharp, with shifted indexing. -/
theorem tm_shifted_sharp (k : ℕ) :
    let q := 6 / (2 * (k : ℝ) + 3)
    dist (tmShadow realGeometry (extremizer q) (-1) k)
        (extremizer q (tmShadow realGeometry (extremizer q) (-1) k)) = q ∧
      dist (tmIter realGeometry (extremizer q) (-1) k)
        (extremizer q (tmIter realGeometry (extremizer q) (-1) k)) = q := by
  dsimp only
  let q := 6 / (2 * (k : ℝ) + 3)
  have hn : (0 : ℝ) < 2 * (k : ℝ) + 3 := by positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hprod : (2 * (k : ℝ) + 3) * q = 6 := by dsimp [q]; field_simp
  have hw : tmShadow realGeometry (extremizer q) (-1) k = -q / 2 := by
    rw [tmShadow_orbit q hq k (le_of_eq hprod)]
    linarith only [hprod]
  have hx : tmIter realGeometry (extremizer q) (-1) k = q / 2 := by
    rw [tmIter_eq_image, hw, extremizer_left q (-q / 2) (le_refl _)]
    ring
  have hleft : extremizer q (-q / 2) = q / 2 := by
    rw [extremizer_left q (-q / 2) (le_refl _)]
    ring
  have hright : extremizer q (q / 2) = -q / 2 := by
    rw [extremizer_right q (q / 2) (by linarith)]
    ring
  have hd : dist (-q / 2) (q / 2) = q := by
    rw [Real.dist_eq, show -q / 2 - q / 2 = -q by ring, abs_neg, abs_of_nonneg hq]
  change dist (tmShadow realGeometry (extremizer q) (-1) k)
      (extremizer q (tmShadow realGeometry (extremizer q) (-1) k)) = q ∧
    dist (tmIter realGeometry (extremizer q) (-1) k)
      (extremizer q (tmIter realGeometry (extremizer q) (-1) k)) = q
  rw [hw, hx, hleft, hright, hd, dist_comm (q / 2) (-q / 2), hd]
  exact ⟨rfl, rfl⟩

/-- Both sharp residuals in the paper's indexing, including `N = 2`. -/
theorem tm_sharp (N : ℕ) (hN : 2 ≤ N) :
    let q := 6 / (2 * (N : ℝ) - 1)
    dist (tmW realGeometry (extremizer q) (-1) N)
        (extremizer q (tmW realGeometry (extremizer q) (-1) N)) = q ∧
      dist (tmX realGeometry (extremizer q) (-1) (N + 1))
        (extremizer q (tmX realGeometry (extremizer q) (-1) (N + 1))) = q := by
  have h := tm_shifted_sharp (N - 2)
  have he : 2 * ((N - 2 : ℕ) : ℝ) + 3 = 2 * (N : ℝ) - 1 := by
    rw [Nat.cast_sub hN]
    norm_num
    ring
  dsimp only at h ⊢
  rw [he] at h
  simpa only [tmW, tmX, show N + 1 - 3 = N - 2 by omega] using h

/-- A nonexpansive real self-map with fixed point zero attains the
Halpern bound at each horizon, with anchor-to-fixed-point distance one. -/
theorem halpern_sharpness (N : ℕ) :
    ∃ T : ℝ → ℝ, LipschitzWith 1 T ∧ T 0 = 0 ∧ dist (-1 : ℝ) 0 = 1 ∧
      dist (halpern realGeometry T (-1) N) (T (halpern realGeometry T (-1) N))
        = 2 / ((N : ℝ) + 1) := by
  refine ⟨extremizer (2 / ((N : ℝ) + 1)), extremizer_nonexpansive _,
    extremizer_fixed _ (by positivity), ?_, halpern_sharp N⟩
  norm_num [Real.dist_eq]

/-- A single real self-map attains both Tikhonov–Mann bounds at each
horizon, with anchor-to-fixed-point distance one. -/
theorem tm_sharpness (N : ℕ) (hN : 2 ≤ N) :
    ∃ T : ℝ → ℝ, LipschitzWith 1 T ∧ T 0 = 0 ∧ dist (-1 : ℝ) 0 = 1 ∧
      dist (tmW realGeometry T (-1) N) (T (tmW realGeometry T (-1) N))
          = 6 / (2 * (N : ℝ) - 1) ∧
        dist (tmX realGeometry T (-1) (N + 1)) (T (tmX realGeometry T (-1) (N + 1)))
          = 6 / (2 * (N : ℝ) - 1) := by
  have hn : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hd : 0 < 2 * (N : ℝ) - 1 := by linarith
  refine ⟨extremizer (6 / (2 * (N : ℝ) - 1)), extremizer_nonexpansive _,
    extremizer_fixed _ (by positivity), ?_, tm_sharp N hN⟩
  norm_num [Real.dist_eq]

end Cat0Bounds
