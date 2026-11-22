import Cat0Bounds.Family
import Cat0Bounds.RealGeometry

namespace Cat0Bounds

/-- The family orbit while it remains on the translation branch. -/
theorem family_orbit (q a l : ℝ) (ha : 1 ≤ a) (hl : 0 ≤ l) (hq : 0 ≤ q)
    (k : ℕ) (hbranch : (a + 1 + 2 * l * (k : ℝ)) * q ≤ 2 * (a + 1)) :
    family realGeometry (extremizer q) (-1) a l k =
      -1 + l * (k : ℝ) * q / (a + 1) := by
  have ha1 : 0 < a + 1 := by linarith
  induction k with
  | zero => simp [family]
  | succ k ih =>
    have hk : (a + 1 + 2 * l * (k : ℝ)) * q ≤ 2 * (a + 1) := by
      push_cast at hbranch
      nlinarith only [hbranch, mul_nonneg hl hq]
    have hratio : l * (k : ℝ) * q / (a + 1) ≤ 1 - q / 2 := by
      apply (div_le_iff₀ ha1).2
      nlinarith only [hk]
    have ht : -1 + l * (k : ℝ) * q / (a + 1) ≤ -q / 2 := by
      linarith only [hratio]
    rw [family_succ, ih hk]
    unfold mann
    rw [extremizer_left q _ ht]
    simp only [realGeometry]
    have hden : 0 < a + (k : ℝ) + 1 := by positivity
    push_cast
    field_simp
    ring

/-- The averaged family point on the same translation branch. -/
theorem familyIter_orbit (q a l : ℝ) (ha : 1 ≤ a) (hl : 0 ≤ l) (hq : 0 ≤ q)
    (k : ℕ) (hbranch : (a + 1 + 2 * l * (k : ℝ)) * q ≤ 2 * (a + 1)) :
    familyIter realGeometry (extremizer q) (-1) a l k =
      -1 + l * ((k : ℝ) + a + 1) * q / (a + 1) := by
  have ha1 : 0 < a + 1 := by linarith
  have hratio : l * (k : ℝ) * q / (a + 1) ≤ 1 - q / 2 := by
    apply (div_le_iff₀ ha1).2
    nlinarith only [hbranch]
  have ht : -1 + l * (k : ℝ) * q / (a + 1) ≤ -q / 2 := by
    linarith only [hratio]
  rw [familyIter_eq_mann, family_orbit q a l ha hl hq k hbranch]
  unfold mann
  rw [extremizer_left q _ ht]
  simp only [realGeometry]
  field_simp
  ring

/-- Equality at the family point for every real parameter and horizon. -/
theorem family_sharp (a l : ℝ) (ha : 1 ≤ a) (hl : 0 ≤ l) (N : ℕ) :
    let q := 2 * (a + 1) / (a + 1 + 2 * l * (N : ℝ))
    dist (family realGeometry (extremizer q) (-1) a l N)
      (extremizer q (family realGeometry (extremizer q) (-1) a l N)) = q := by
  dsimp only
  let q := 2 * (a + 1) / (a + 1 + 2 * l * (N : ℝ))
  have ha1 : 0 < a + 1 := by linarith
  have hden : 0 < a + 1 + 2 * l * (N : ℝ) := by positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hprod : (a + 1 + 2 * l * (N : ℝ)) * q = 2 * (a + 1) := by
    dsimp [q]
    field_simp
  have hx : family realGeometry (extremizer q) (-1) a l N = -q / 2 := by
    rw [family_orbit q a l ha hl hq N (le_of_eq hprod)]
    have hratio : l * (N : ℝ) * q / (a + 1) = 1 - q / 2 := by
      apply (div_eq_iff (ne_of_gt ha1)).2
      nlinarith only [hprod]
    linarith only [hratio]
  change dist (family realGeometry (extremizer q) (-1) a l N)
    (extremizer q (family realGeometry (extremizer q) (-1) a l N)) = q
  rw [hx, extremizer_left q (-q / 2) (le_refl _)]
  rw [Real.dist_eq, show -q / 2 - (-q / 2 + q) = -q by ring,
    abs_neg, abs_of_nonneg hq]

/-- At unit averaging, the same sharp constant is attained at the endpoint. -/
theorem familyIter_unit_sharp (a : ℝ) (ha : 1 ≤ a) (N : ℕ) :
    let q := 2 * (a + 1) / (a + 1 + 2 * (N : ℝ))
    dist (familyIter realGeometry (extremizer q) (-1) a 1 N)
      (extremizer q (familyIter realGeometry (extremizer q) (-1) a 1 N)) = q := by
  dsimp only
  let q := 2 * (a + 1) / (a + 1 + 2 * (N : ℝ))
  have ha1 : 0 < a + 1 := by linarith
  have hden : 0 < a + 1 + 2 * (N : ℝ) := by positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hprod : (a + 1 + 2 * (N : ℝ)) * q = 2 * (a + 1) := by
    dsimp [q]
    field_simp
  have hbranch : (a + 1 + 2 * 1 * (N : ℝ)) * q ≤ 2 * (a + 1) := by
    simpa using le_of_eq hprod
  have hy : familyIter realGeometry (extremizer q) (-1) a 1 N = q / 2 := by
    rw [familyIter_orbit q a 1 ha (by norm_num) hq N hbranch]
    have hratio : ((N : ℝ) + a + 1) * q / (a + 1) = 1 + q / 2 := by
      apply (div_eq_iff (ne_of_gt ha1)).2
      nlinarith only [hprod]
    simp only [one_mul]
    linarith only [hratio]
  change dist (familyIter realGeometry (extremizer q) (-1) a 1 N)
    (extremizer q (familyIter realGeometry (extremizer q) (-1) a 1 N)) = q
  rw [hy, extremizer_right q (q / 2) (by linarith only [hq])]
  rw [Real.dist_eq, show q / 2 - -(q / 2) = q by ring, abs_of_nonneg hq]

/-- The endpoint lower example for every family parameter and horizon. -/
theorem familyIter_lower_example (a l : ℝ) (ha : 1 ≤ a) (hl : 0 ≤ l)
    (N : ℕ) :
    let q := 2 * (a + 1) / (a + 1 + 2 * l * ((N : ℝ) + a + 1))
    dist (familyIter realGeometry (extremizer q) (-1) a l N)
      (extremizer q (familyIter realGeometry (extremizer q) (-1) a l N)) = q := by
  dsimp only
  let q := 2 * (a + 1) / (a + 1 + 2 * l * ((N : ℝ) + a + 1))
  have ha1 : 0 < a + 1 := by linarith
  have hden : 0 < a + 1 + 2 * l * ((N : ℝ) + a + 1) := by positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hprod : (a + 1 + 2 * l * ((N : ℝ) + a + 1)) * q = 2 * (a + 1) := by
    dsimp [q]
    field_simp
  have hbranch : (a + 1 + 2 * l * (N : ℝ)) * q ≤ 2 * (a + 1) := by
    nlinarith only [hprod, mul_nonneg (mul_nonneg hl (le_of_lt ha1)) hq]
  have hy : familyIter realGeometry (extremizer q) (-1) a l N = -q / 2 := by
    rw [familyIter_orbit q a l ha hl hq N hbranch]
    have hratio : l * ((N : ℝ) + a + 1) * q / (a + 1) = 1 - q / 2 := by
      apply (div_eq_iff (ne_of_gt ha1)).2
      nlinarith only [hprod]
    linarith only [hratio]
  change dist (familyIter realGeometry (extremizer q) (-1) a l N)
    (extremizer q (familyIter realGeometry (extremizer q) (-1) a l N)) = q
  rw [hy, extremizer_left q (-q / 2) (le_refl _)]
  rw [Real.dist_eq, show -q / 2 - (-q / 2 + q) = -q by ring,
    abs_neg, abs_of_nonneg hq]

/-- A nonexpansive real map with fixed point zero attains the family bound. -/
theorem family_sharpness (a l : ℝ) (ha : 1 ≤ a) (hl : 0 < l)
    (N : ℕ) :
    ∃ T : ℝ → ℝ, LipschitzWith 1 T ∧ T 0 = 0 ∧ dist (-1 : ℝ) 0 = 1 ∧
      dist (family realGeometry T (-1) a l N)
        (T (family realGeometry T (-1) a l N)) =
          2 * (a + 1) / (a + 1 + 2 * l * (N : ℝ)) := by
  have ha1 : 0 < a + 1 := by linarith
  have hden : 0 < a + 1 + 2 * l * (N : ℝ) := by positivity
  refine ⟨extremizer (2 * (a + 1) / (a + 1 + 2 * l * (N : ℝ))),
    extremizer_nonexpansive _, extremizer_fixed _ (by positivity), ?_,
    family_sharp a l ha (le_of_lt hl) N⟩
  norm_num [Real.dist_eq]

end Cat0Bounds
