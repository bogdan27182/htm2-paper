import Cat0Bounds.FamilySharpness

/-! The endpoint worst-case supremum and its exact asymptotic constant.

The admissible class consists of all metric carriers in an arbitrary fixed
universe, equipped with the project's explicit Geometry hypotheses.
Normalization uses the actual residual divided by dist u p, with dist u p > 0.
The real-line lower examples are lifted to the chosen universe, so the
supremum is neither a supremum only over real maps nor an assumed sandwich.
-/

namespace Cat0Bounds

open Filter

universe v

variable {X : Type v} [MetricSpace X]

def endpointRealizes (G : Geometry X) (T : X → X) (u p : X)
    (a l : ℝ) (N : ℕ) (r : ℝ) : Prop :=
  LipschitzWith 1 T ∧ T p = p ∧ 0 < dist u p ∧
    r = dist (familyIter G T u a l N) (T (familyIter G T u a l N)) / dist u p

def endpointResidualSet (a l : ℝ) (N : ℕ) : Set ℝ :=
  {r | ∃ (X : Type v) (m : MetricSpace X) (G : @Geometry X m)
    (T : X → X) (u p : X), @endpointRealizes X m G T u p a l N r}

noncomputable def endpointWorstCase (a l : ℝ) (N : ℕ) : ℝ :=
  sSup (endpointResidualSet.{v} a l N)

theorem endpoint_ratio_le (G : Geometry X) {T : X → X} (hT : LipschitzWith 1 T)
    (u p : X) (hp : T p = p) (hD : 0 < dist u p) (a l : ℝ)
    (ha : 1 ≤ a) (hl0 : 0 < l) (hl1 : l ≤ 1) (N : ℕ) :
    dist (familyIter G T u a l N) (T (familyIter G T u a l N)) / dist u p
      ≤ 2 * (a + 1) / (a + 1 + 2 * l * (N : ℝ)) := by
  have hap : 0 < a + 1 := by linarith
  have hden : 0 < a + 1 + 2 * l * (N : ℝ) := by positivity
  have hb := family_endpoint_bound G hT u p a l ha hl0 hl1 N
  simp only [hp, dist_self, zero_add] at hb
  apply (div_le_iff₀ hD).2
  calc
    _ ≤ 2 * dist u p / familyKappa a l N := hb
    _ = _ := by
      unfold familyKappa
      field_simp [ne_of_gt hap, ne_of_gt hden]

theorem endpointResidualSet_le (a l : ℝ) (ha : 1 ≤ a) (hl0 : 0 < l) (hl1 : l ≤ 1)
    (N : ℕ) {r : ℝ} (hr : r ∈ endpointResidualSet.{v} a l N) :
    r ≤ 2 * (a + 1) / (a + 1 + 2 * l * (N : ℝ)) := by
  obtain ⟨X, m, G, T, u, p, hT, hp, hD, rfl⟩ := hr
  let _ := m
  exact endpoint_ratio_le G hT u p hp hD a l ha hl0 hl1 N

theorem endpointResidualSet_bddAbove (a l : ℝ) (ha : 1 ≤ a)
    (hl0 : 0 < l) (hl1 : l ≤ 1) (N : ℕ) :
    BddAbove (endpointResidualSet.{v} a l N) :=
  ⟨2 * (a + 1) / (a + 1 + 2 * l * (N : ℝ)),
    fun _ hr => endpointResidualSet_le a l ha hl0 hl1 N hr⟩

noncomputable def liftedRealGeometry : Geometry (ULift.{v} ℝ) where
  mix t x y := ⟨realGeometry.mix t x.down y.down⟩
  dist_left t x y ht0 ht1 := realGeometry.dist_left t x.down y.down ht0 ht1
  dist_right t x y ht0 ht1 := realGeometry.dist_right t x.down y.down ht0 ht1
  cn t x y z ht0 ht1 := realGeometry.cn t x.down y.down z.down ht0 ht1
  four_point x y z w := realGeometry.four_point x.down y.down z.down w.down

noncomputable def liftedExtremizer (q : ℝ) (x : ULift.{v} ℝ) : ULift.{v} ℝ :=
  ⟨extremizer q x.down⟩

theorem liftedFamily_down (q a l : ℝ) (N : ℕ) :
    (family liftedRealGeometry (liftedExtremizer q) (ULift.up (-1)) a l N).down =
      family realGeometry (extremizer q) (-1) a l N := by
  induction N with
  | zero => rfl
  | succ k ih =>
      rw [family_succ, family_succ]
      change realGeometry.mix (((k : ℝ) + 1) / (a + (k : ℝ) + 1)) (-1)
          (realGeometry.mix l
            (family liftedRealGeometry (liftedExtremizer q) (ULift.up (-1)) a l k).down
            (extremizer q
              (family liftedRealGeometry (liftedExtremizer q) (ULift.up (-1)) a l k).down)) =
        realGeometry.mix (((k : ℝ) + 1) / (a + (k : ℝ) + 1)) (-1)
          (mann realGeometry (extremizer q) l (family realGeometry (extremizer q) (-1) a l k))
      rw [ih]
      rfl

theorem liftedFamilyIter_down (q a l : ℝ) (N : ℕ) :
    (familyIter liftedRealGeometry (liftedExtremizer q) (ULift.up (-1)) a l N).down =
      familyIter realGeometry (extremizer q) (-1) a l N := by
  rw [familyIter_eq_mann, familyIter_eq_mann]
  change realGeometry.mix l
      (family liftedRealGeometry (liftedExtremizer q) (ULift.up (-1)) a l N).down
      (extremizer q
        (family liftedRealGeometry (liftedExtremizer q) (ULift.up (-1)) a l N).down) = _
  rw [liftedFamily_down]
  rfl

/-- The explicit lower example belongs to the full normalized admissible set. -/
theorem endpoint_lower_mem (a l : ℝ) (ha : 1 ≤ a) (hl : 0 ≤ l) (N : ℕ) :
    2 * (a + 1) / (a + 1 + 2 * l * ((N : ℝ) + a + 1))
      ∈ endpointResidualSet.{v} a l N := by
  let q := 2 * (a + 1) / (a + 1 + 2 * l * ((N : ℝ) + a + 1))
  have hap : 0 < a + 1 := by linarith
  have hq : 0 ≤ q := by dsimp [q]; positivity
  refine ⟨ULift.{v} ℝ, inferInstance, liftedRealGeometry, liftedExtremizer q,
    ULift.up (-1), ULift.up 0, ?_, ?_, ?_, ?_⟩
  · apply LipschitzWith.mk_one
    intro x y
    exact nonexpansive_dist (extremizer_nonexpansive q) x.down y.down
  · apply ULift.ext
    exact extremizer_fixed q hq
  · change 0 < dist (-1 : ℝ) 0
    norm_num [Real.dist_eq]
  · change q = dist
      (familyIter liftedRealGeometry (liftedExtremizer q) (ULift.up (-1)) a l N).down
      (extremizer q
        (familyIter liftedRealGeometry (liftedExtremizer q) (ULift.up (-1)) a l N).down) /
      dist (-1 : ℝ) 0
    rw [liftedFamilyIter_down]
    norm_num only [Real.dist_eq, sub_zero, abs_neg, abs_one, div_one]
    exact (familyIter_lower_example a l ha hl N).symm

theorem endpointResidualSet_nonempty (a l : ℝ) (ha : 1 ≤ a) (hl : 0 ≤ l) (N : ℕ) :
    (endpointResidualSet.{v} a l N).Nonempty :=
  ⟨_, endpoint_lower_mem a l ha hl N⟩

/-- The manuscript's lower and upper bounds for the endpoint supremum. -/
theorem endpointWorstCase_sandwich (a l : ℝ) (ha : 1 ≤ a)
    (hl0 : 0 < l) (hl1 : l ≤ 1) (N : ℕ) :
    2 * (a + 1) / (a + 1 + 2 * l * ((N : ℝ) + a + 1))
        ≤ endpointWorstCase.{v} a l N ∧
      endpointWorstCase.{v} a l N ≤ 2 * (a + 1) / (a + 1 + 2 * l * (N : ℝ)) := by
  constructor
  · exact le_csSup (endpointResidualSet_bddAbove a l ha hl0 hl1 N)
      (endpoint_lower_mem a l ha (le_of_lt hl0) N)
  · exact csSup_le (endpointResidualSet_nonempty a l ha (le_of_lt hl0) N)
      (fun _ hr => endpointResidualSet_le a l ha hl0 hl1 N hr)

/-- The exact endpoint asymptotic constant for the genuine worst-case supremum. -/
theorem endpointWorstCase_asymptotic (a l : ℝ) (ha : 1 ≤ a)
    (hl0 : 0 < l) (hl1 : l ≤ 1) :
    Tendsto (fun n : ℕ => (n : ℝ) * endpointWorstCase.{v} a l n)
      atTop (nhds ((a + 1) / l)) := by
  have htwo : 2 * l ≠ 0 := ne_of_gt (by positivity)
  have hlimit : 2 * (a + 1) / (2 * l) = (a + 1) / l := by ring
  have hlower :
      Tendsto (fun n : ℕ => (n : ℝ) *
        (2 * (a + 1) / (a + 1 + 2 * l * ((n : ℝ) + a + 1))))
        atTop (nhds ((a + 1) / l)) := by
    have h := tendsto_add_mul_div_add_mul_atTop_nhds
      (0 : ℝ) (a + 1 + 2 * l * (a + 1)) (2 * (a + 1)) htwo
    rw [hlimit] at h
    convert h using 1
    ext n
    rw [← mul_div_assoc]
    congr 1 <;> ring
  have hupper :
      Tendsto (fun n : ℕ => (n : ℝ) *
        (2 * (a + 1) / (a + 1 + 2 * l * (n : ℝ))))
        atTop (nhds ((a + 1) / l)) := by
    have h := tendsto_add_mul_div_add_mul_atTop_nhds
      (0 : ℝ) (a + 1) (2 * (a + 1)) htwo
    rw [hlimit] at h
    convert h using 1
    ext n
    ring
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlower hupper
  · intro n
    exact mul_le_mul_of_nonneg_left (endpointWorstCase_sandwich a l ha hl0 hl1 n).1
      (Nat.cast_nonneg n)
  · intro n
    exact mul_le_mul_of_nonneg_left (endpointWorstCase_sandwich a l ha hl0 hl1 n).2
      (Nat.cast_nonneg n)

end Cat0Bounds
