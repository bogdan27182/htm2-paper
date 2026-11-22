import Mathlib

/-! Explicit geometric hypotheses used by the paper.

`mix t a b` denotes the point `(1-t)a ⊕ t b`. The carrier can be a
convex subset equipped with its induced metric. No completeness assumption
is made. The CN and four-point inequalities are hypotheses, not axioms
asserted for arbitrary metric spaces and not a definition imported from a
CAT(0) library.
-/

namespace Cat0Bounds

structure Geometry (X : Type*) [MetricSpace X] where
  mix : ℝ → X → X → X
  dist_left : ∀ (t : ℝ) (a b : X), 0 ≤ t → t ≤ 1 →
    dist a (mix t a b) = t * dist a b
  dist_right : ∀ (t : ℝ) (a b : X), 0 ≤ t → t ≤ 1 →
    dist (mix t a b) b = (1 - t) * dist a b
  cn : ∀ (t : ℝ) (a b z : X), 0 ≤ t → t ≤ 1 →
    dist z (mix t a b) ^ 2 ≤
      (1 - t) * dist z a ^ 2 + t * dist z b ^ 2
        - t * (1 - t) * dist a b ^ 2
  four_point : ∀ (a b c e : X),
    dist a e ^ 2 + dist b c ^ 2 - dist a c ^ 2 - dist b e ^ 2
      ≤ 2 * dist a b * dist c e

variable {X : Type*} [MetricSpace X]

theorem nonexpansive_dist {T : X → X} (hT : LipschitzWith 1 T) (x y : X) :
    dist (T x) (T y) ≤ dist x y := by
  simpa using hT.dist_le_mul x y

theorem nonexpansive_sq {T : X → X} (hT : LipschitzWith 1 T) (x y : X) :
    dist (T x) (T y) ^ 2 ≤ dist x y ^ 2 := by
  gcongr
  exact nonexpansive_dist hT x y

/-- The geometric part of Lemma 2.1. -/
theorem endpoint (G : Geometry X) {T : X → X} (hT : LipschitzWith 1 T)
    {p : X} (hp : T p = p) (u z : X) :
    dist u (T z) ^ 2 - dist u z ^ 2 ≤ 2 * dist u p * dist z (T z) := by
  have hc := G.four_point u p z (T z)
  have hpdist : dist p (T z) ^ 2 ≤ dist p z ^ 2 := by
    simpa only [hp] using nonexpansive_sq hT p z
  linarith

/-- The two successive CN comparisons used in Lemma 3.1. -/
theorem two_cn (G : Geometry X) (u x y y' : X) (s : ℝ)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hne : dist y y' ≤ dist x (G.mix s u y)) :
    dist (G.mix s u y) y' ^ 2 ≤
      (1 - s) * dist u y' ^ 2
        + (1 - s) * s * dist u x ^ 2 + s ^ 2 * dist x y ^ 2
        - (1 - s) * s * (1 + s) * dist u y ^ 2 := by
  have h1 := G.cn s u y y' hs0 hs1
  have h2 := G.cn s u y x hs0 hs1
  have hne2 : dist y y' ^ 2 ≤ dist x (G.mix s u y) ^ 2 := by
    gcongr
  have hm1 := mul_le_mul_of_nonneg_left hne2 hs0
  have hm2 := mul_le_mul_of_nonneg_left h2 hs0
  simp only [dist_comm y' (G.mix s u y), dist_comm y' u,
    dist_comm y' y] at h1
  rw [dist_comm x u] at hm2
  nlinarith only [h1, hm1, hm2]

end Cat0Bounds
