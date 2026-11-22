import Cat0Bounds.FamilySharpness
import Cat0Bounds.Adaptive
import Cat0Bounds.Stronger

namespace Cat0Bounds

variable {X : Type*} [MetricSpace X]

/-- Averaging supplies the stronger fixed-point inequality in any of the
geometries already admitted by the paper. -/
theorem mann_stronger (G : Geometry X) {T : X → X} (hT : LipschitzWith 1 T)
    {p : X} (hp : T p = p) (l : ℝ) (hl0 : 0 < l) (hl1 : l ≤ 1) (z : X) :
    dist p (mann G T l z) ^ 2 ≤ dist p z ^ 2
      - (1 - l) / l * dist z (mann G T l z) ^ 2 := by
  have hcn := G.cn l z (T z) p (le_of_lt hl0) hl1
  have ht : dist p (T z) ^ 2 ≤ dist p z ^ 2 := by
    simpa only [hp] using nonexpansive_sq hT p z
  have hm := mul_le_mul_of_nonneg_left ht (le_of_lt hl0)
  change dist p (mann G T l z) ^ 2 ≤ _ at hcn
  rw [mann_dist G T l (le_of_lt hl0) hl1, mul_pow]
  have he : (1 - l) / l * l ^ 2 = l * (1 - l) := by field_simp
  rw [← mul_assoc, he]
  nlinarith only [hcn, hm]

/-- This averaged V-map is the stronger real-line equality example.
On its left branch it translates by q; its right slope is (sigma-1)/(sigma+1). -/
noncomputable def strongerExtremizer (q σ : ℝ) : ℝ → ℝ :=
  mann realGeometry (extremizer ((σ + 1) * q)) (1 / (σ + 1))

theorem strongerExtremizer_nonexpansive (q σ : ℝ) (hσ : 0 ≤ σ) :
    LipschitzWith 1 (strongerExtremizer q σ) := by
  have hp : 0 < σ + 1 := by linarith
  apply mann_nonexpansive realGeometry (extremizer_nonexpansive _) _ (by positivity)
  apply (div_le_iff₀ hp).2
  linarith

theorem strongerExtremizer_fixed (q σ : ℝ) (hq : 0 ≤ q) (hσ : 0 ≤ σ) :
    strongerExtremizer q σ 0 = 0 := by
  unfold strongerExtremizer mann
  rw [extremizer_fixed _ (by positivity)]
  simp [realGeometry]

theorem strongerExtremizer_strong (q σ : ℝ) (hq : 0 ≤ q) (hσ : 0 ≤ σ) (z : ℝ) :
    dist 0 (strongerExtremizer q σ z) ^ 2 ≤ dist 0 z ^ 2
      - σ * dist z (strongerExtremizer q σ z) ^ 2 := by
  have hp : 0 < σ + 1 := by linarith
  have hμ : 0 < 1 / (σ + 1) := by positivity
  have hμ1 : 1 / (σ + 1) ≤ 1 := by apply (div_le_iff₀ hp).2; linarith
  have h := mann_stronger realGeometry (extremizer_nonexpansive ((σ + 1) * q))
    (extremizer_fixed _ (by positivity)) (1 / (σ + 1)) hμ hμ1 z
  have hc : (1 - 1 / (σ + 1)) / (1 / (σ + 1)) = σ := by field_simp; ring
  rw [hc] at h
  exact h

theorem strongerExtremizer_left (q σ t : ℝ) (hσ : 0 ≤ σ)
    (ht : t ≤ -(σ + 1) * q / 2) : strongerExtremizer q σ t = t + q := by
  have hp : 0 < σ + 1 := by linarith
  unfold strongerExtremizer mann
  rw [extremizer_left _ _ (by linarith only [ht])]
  simp only [realGeometry]
  field_simp
  ring

theorem stronger_family_orbit (q σ a l : ℝ) (ha : 1 ≤ a) (hl : 0 ≤ l)
    (hq : 0 ≤ q) (hσ : 0 ≤ σ) (k : ℕ)
    (hbranch : ((σ + 1) * (a + 1) + 2 * l * (k : ℝ)) * q ≤ 2 * (a + 1)) :
    family realGeometry (strongerExtremizer q σ) (-1) a l k =
      -1 + l * (k : ℝ) * q / (a + 1) := by
  have ha1 : 0 < a + 1 := by linarith
  induction k with
  | zero => simp [family]
  | succ k ih =>
    have hk : ((σ + 1) * (a + 1) + 2 * l * (k : ℝ)) * q ≤ 2 * (a + 1) := by
      push_cast at hbranch
      nlinarith only [hbranch, mul_nonneg hl hq]
    have hratio : l * (k : ℝ) * q / (a + 1) ≤ 1 - (σ + 1) * q / 2 := by
      apply (div_le_iff₀ ha1).2
      nlinarith only [hk]
    have ht : -1 + l * (k : ℝ) * q / (a + 1) ≤ -(σ + 1) * q / 2 := by
      linarith only [hratio]
    rw [family_succ, ih hk]
    unfold mann
    rw [strongerExtremizer_left q σ _ hσ ht]
    simp only [realGeometry]
    have hden : 0 < a + (k : ℝ) + 1 := by positivity
    push_cast
    field_simp
    ring

theorem stronger_family_sharp (a l σ : ℝ) (ha : 1 ≤ a) (hl : 0 ≤ l)
    (hσ : 0 ≤ σ) (N : ℕ) :
    let q := 2 / (familyKappa a l N + σ)
    dist (family realGeometry (strongerExtremizer q σ) (-1) a l N)
      (strongerExtremizer q σ (family realGeometry (strongerExtremizer q σ) (-1) a l N)) = q := by
  dsimp only
  let q := 2 / (familyKappa a l N + σ)
  have ha1 : 0 < a + 1 := by linarith
  have hden : 0 < familyKappa a l N + σ := by
    have := familyKappa_pos a l ha hl N
    linarith
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hprod : ((σ + 1) * (a + 1) + 2 * l * (N : ℝ)) * q = 2 * (a + 1) := by
    dsimp [q, familyKappa]
    have hd : 0 < 1 + 2 * l * (N : ℝ) / (a + 1) + σ := hden
    field_simp
    ring
  have hx : family realGeometry (strongerExtremizer q σ) (-1) a l N =
      -1 + l * (N : ℝ) * q / (a + 1) :=
    stronger_family_orbit q σ a l ha hl hq hσ N (le_of_eq hprod)
  have ht : -1 + l * (N : ℝ) * q / (a + 1) ≤ -(σ + 1) * q / 2 := by
    have he : l * (N : ℝ) * q / (a + 1) = 1 - (σ + 1) * q / 2 := by
      apply (div_eq_iff (ne_of_gt ha1)).2
      nlinarith only [hprod]
    linarith only [he]
  change dist (family realGeometry (strongerExtremizer q σ) (-1) a l N)
    (strongerExtremizer q σ (family realGeometry (strongerExtremizer q σ) (-1) a l N)) = q
  rw [hx, strongerExtremizer_left q σ _ hσ ht, Real.dist_eq]
  rw [show -1 + l * (N : ℝ) * q / (a + 1) -
    (-1 + l * (N : ℝ) * q / (a + 1) + q) = -q by ring, abs_neg, abs_of_nonneg hq]

theorem translation_adaptiveCoeff (T : ℝ → ℝ) (q : ℝ) (hq : 0 < q) (k : ℕ)
    (ht : T (-1 + (k : ℝ) * q / 2) = -1 + (k : ℝ) * q / 2 + q) :
    adaptiveCoeff T (-1) (-1 + (k : ℝ) * q / 2) = (k : ℝ) + 1 := by
  unfold adaptiveCoeff anchoredPhi
  rw [ht]
  simp only [Real.dist_eq, sq_abs]
  have hnum : (-1 - (-1 + (k : ℝ) * q / 2 + q)) ^ 2
      - (-1 - (-1 + (k : ℝ) * q / 2)) ^ 2 = ((k : ℝ) + 1) * q ^ 2 := by ring
  have hden : (-1 + (k : ℝ) * q / 2 - (-1 + (k : ℝ) * q / 2 + q)) ^ 2 = q ^ 2 := by ring
  rw [hnum, hden]
  field_simp [ne_of_gt hq]

theorem stronger_adaptive_orbit (q σ : ℝ) (hq : 0 < q) (hσ : 0 ≤ σ) (k : ℕ)
    (hbranch : ((k : ℝ) + 1 + σ) * q ≤ 2) :
    adaptive realGeometry (strongerExtremizer q σ) (-1) k = -1 + (k : ℝ) * q / 2 := by
  induction k with
  | zero => simp [adaptive]
  | succ k ih =>
    have hk : ((k : ℝ) + 1 + σ) * q ≤ 2 := by
      push_cast at hbranch
      nlinarith only [hbranch, hq]
    have ht : -1 + (k : ℝ) * q / 2 ≤ -(σ + 1) * q / 2 := by linarith only [hk]
    have he := strongerExtremizer_left q σ _ hσ ht
    have hnonfixed : strongerExtremizer q σ (-1 + (k : ℝ) * q / 2) ≠
        -1 + (k : ℝ) * q / 2 := by rw [he]; linarith
    change adaptiveStep realGeometry (strongerExtremizer q σ) (-1)
      (adaptive realGeometry (strongerExtremizer q σ) (-1) k) = _
    rw [ih hk, adaptiveStep_of_nonfixed _ _ _ _ hnonfixed,
      translation_adaptiveCoeff _ q hq k he, he]
    simp only [realGeometry]
    have hd : 0 < (k : ℝ) + 1 + 1 := by positivity
    push_cast
    field_simp
    ring

theorem stronger_adaptive_sharp (σ : ℝ) (hσ : 0 ≤ σ) (N : ℕ) :
    let q := 2 / ((N : ℝ) + 1 + σ)
    adaptiveCoeff (strongerExtremizer q σ) (-1)
        (adaptive realGeometry (strongerExtremizer q σ) (-1) N) = (N : ℝ) + 1 ∧
      dist (adaptive realGeometry (strongerExtremizer q σ) (-1) N)
        (strongerExtremizer q σ (adaptive realGeometry (strongerExtremizer q σ) (-1) N)) = q := by
  dsimp only
  let q := 2 / ((N : ℝ) + 1 + σ)
  have hden : 0 < (N : ℝ) + 1 + σ := by positivity
  have hq : 0 < q := by dsimp [q]; positivity
  have hprod : ((N : ℝ) + 1 + σ) * q = 2 := by dsimp [q]; field_simp
  have horbit := stronger_adaptive_orbit q σ hq hσ N (le_of_eq hprod)
  have ht : -1 + (N : ℝ) * q / 2 ≤ -(σ + 1) * q / 2 := by linarith only [hprod]
  have he := strongerExtremizer_left q σ _ hσ ht
  change adaptiveCoeff (strongerExtremizer q σ) (-1)
      (adaptive realGeometry (strongerExtremizer q σ) (-1) N) = (N : ℝ) + 1 ∧
    dist (adaptive realGeometry (strongerExtremizer q σ) (-1) N)
      (strongerExtremizer q σ (adaptive realGeometry (strongerExtremizer q σ) (-1) N)) = q
  rw [horbit]
  constructor
  · exact translation_adaptiveCoeff _ q hq N he
  · rw [he, Real.dist_eq,
      show -1 + (N : ℝ) * q / 2 - (-1 + (N : ℝ) * q / 2 + q) = -q by ring,
      abs_neg, abs_of_nonneg (le_of_lt hq)]

theorem stronger_family_sharpness (a l σ : ℝ) (ha : 1 ≤ a) (hl : 0 ≤ l)
    (hσ : 0 ≤ σ) (N : ℕ) :
    ∃ T : ℝ → ℝ, LipschitzWith 1 T ∧ T 0 = 0 ∧
      (∀ z, dist 0 (T z) ^ 2 ≤ dist 0 z ^ 2 - σ * dist z (T z) ^ 2) ∧
      dist (family realGeometry T (-1) a l N) (T (family realGeometry T (-1) a l N))
        = 2 / (familyKappa a l N + σ) := by
  let q := 2 / (familyKappa a l N + σ)
  have hq : 0 ≤ q := by
    have := familyKappa_pos a l ha hl N
    dsimp [q]
    positivity
  exact ⟨strongerExtremizer q σ, strongerExtremizer_nonexpansive q σ hσ,
    strongerExtremizer_fixed q σ hq hσ, strongerExtremizer_strong q σ hq hσ,
    stronger_family_sharp a l σ ha hl hσ N⟩

theorem stronger_adaptive_sharpness (σ : ℝ) (hσ : 0 ≤ σ) (N : ℕ) :
    ∃ T : ℝ → ℝ, LipschitzWith 1 T ∧ T 0 = 0 ∧
      (∀ z, dist 0 (T z) ^ 2 ≤ dist 0 z ^ 2 - σ * dist z (T z) ^ 2) ∧
      adaptiveCoeff T (-1) (adaptive realGeometry T (-1) N) = (N : ℝ) + 1 ∧
      dist (adaptive realGeometry T (-1) N) (T (adaptive realGeometry T (-1) N))
        = 2 / (adaptiveCoeff T (-1) (adaptive realGeometry T (-1) N) + σ) := by
  let q := 2 / ((N : ℝ) + 1 + σ)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hs := stronger_adaptive_sharp σ hσ N
  refine ⟨strongerExtremizer q σ, strongerExtremizer_nonexpansive q σ hσ,
    strongerExtremizer_fixed q σ hq hσ, strongerExtremizer_strong q σ hq hσ, hs.1, ?_⟩
  rw [hs.1]
  exact hs.2

end Cat0Bounds
